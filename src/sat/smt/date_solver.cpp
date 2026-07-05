/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates (SAT/EUF core).

Author:

    Z3 date theory extension 2026-07-05

--*/
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_value.h"

namespace dates {

    solver::solver(euf::solver& ctx, euf::theory_id id):
        th_euf_solver(ctx, ctx.get_manager().get_family_name(id), id),
        u(m),
        a(m) {
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        euf::theory_var v = th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, v);
        return v;
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        force_push();
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        auto lit = expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e) {
        force_push();
        visit_rec(m, e, false, false);
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());
    }

    bool solver::visit(expr* e) {
        if (visited(e))
            return true;
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        if (!n)
            n = mk_enode(e);
        if (n->is_attached_to(get_id()))
            return true;
        track_date(n);
        internalize_date_op(to_app(e));
        return true;
    }

    void solver::apply_sort_cnstr(euf::enode* n, sort* s) {
        SASSERT(u.is_date(s));
        force_push();
        track_date(n);
    }

    /**
       \brief Attach a theory variable, and for Date-sorted nodes assert the
       tautology (<= epoch(d) 0) or (>= epoch(d) 0) so that epoch(d) is
       registered with the arithmetic solver and always has a value in the
       arithmetic model.
    */
    void solver::track_date(euf::enode* n) {
        if (is_attached_to_var(n))
            return;
        mk_var(n);
        if (!u.is_date(n->get_expr()))
            return;
        expr_ref ep(u.mk_epoch(n->get_expr()), m);
        expr_ref zero(a.mk_int(0), m);
        expr_ref le(a.mk_le(ep, zero), m);
        expr_ref ge(a.mk_ge(ep, zero), m);
        add_clause(mk_literal(le), mk_literal(ge));
    }

    void solver::assert_axiom_eq(expr* lhs, expr* rhs) {
        expr_ref _lhs(lhs, m), _rhs(rhs, m);
        rewrite(_rhs);
        if (_lhs == _rhs)
            return;
        add_unit(eq_internalize(_lhs, _rhs));
    }

    void solver::internalize_date_op(app* t) {
        switch (t->get_decl_kind()) {
        case OP_DATE_MK:
            assert_axiom_eq(u.mk_epoch(t),
                            u.mk_epoch_of_ymd(t->get_arg(0), t->get_arg(1), t->get_arg(2)));
            break;
        case OP_DATE_ADD: {
            expr_ref ep(u.mk_epoch(t->get_arg(0)), m);
            assert_axiom_eq(u.mk_epoch(t),
                            u.mk_epoch_of_add(ep, t->get_arg(1), t->get_arg(2), t->get_arg(3)));
            break;
        }
        case OP_DATE_SUB: {
            // date.sub is date.add with negated offsets
            expr_ref ep(u.mk_epoch(t->get_arg(0)), m);
            expr_ref npy(a.mk_uminus(t->get_arg(1)), m);
            expr_ref npm(a.mk_uminus(t->get_arg(2)), m);
            expr_ref npd(a.mk_uminus(t->get_arg(3)), m);
            assert_axiom_eq(u.mk_epoch(t), u.mk_epoch_of_add(ep, npy, npm, npd));
            break;
        }
        case OP_DATE_YEAR: {
            expr_ref ep(u.mk_epoch(t->get_arg(0)), m);
            assert_axiom_eq(t, u.mk_year_of_epoch(ep));
            assert_civil_identity(t->get_arg(0));
            break;
        }
        case OP_DATE_MONTH: {
            expr_ref ep(u.mk_epoch(t->get_arg(0)), m);
            assert_axiom_eq(t, u.mk_month_of_epoch(ep));
            assert_civil_identity(t->get_arg(0));
            break;
        }
        case OP_DATE_DAY: {
            expr_ref ep(u.mk_epoch(t->get_arg(0)), m);
            assert_axiom_eq(t, u.mk_day_of_epoch(ep));
            assert_civil_identity(t->get_arg(0));
            break;
        }
        case OP_DATE_LT:
        case OP_DATE_LE:
        case OP_DATE_GT:
        case OP_DATE_GE: {
            expr_ref ep1(u.mk_epoch(t->get_arg(0)), m);
            expr_ref ep2(u.mk_epoch(t->get_arg(1)), m);
            expr_ref ineq(m);
            switch (t->get_decl_kind()) {
            case OP_DATE_LT: ineq = a.mk_lt(ep1, ep2); break;
            case OP_DATE_LE: ineq = a.mk_le(ep1, ep2); break;
            case OP_DATE_GT: ineq = a.mk_lt(ep2, ep1); break;
            case OP_DATE_GE: ineq = a.mk_le(ep2, ep1); break;
            default: UNREACHABLE();
            }
            rewrite(ineq);
            sat::literal alit = expr2literal(t);
            if (m.is_true(ineq))
                add_unit(alit);
            else if (m.is_false(ineq))
                add_unit(~alit);
            else
                add_equiv(alit, mk_literal(ineq));
            break;
        }
        case OP_DATE_EPOCH:
            // definitional axioms are attached to the argument
            break;
        default:
            UNREACHABLE();
        }
    }

    /**
       \brief Assert epoch(d) = days-from-civil(year, month, day of epoch(d))
       together with range bounds on the components. These are valid facts
       of the calendar bijection; providing them as axioms lets equalities
       between components propagate to equalities between epochs by
       congruence, instead of requiring the arithmetic solver to re-derive
       injectivity of the calendar map.
    */
    void solver::assert_civil_identity(expr* d) {
        expr_ref ep(u.mk_epoch(d), m);
        assert_axiom_eq(ep, u.mk_civil_roundtrip(ep));
        expr_ref mo = u.mk_month_of_epoch(ep);
        expr_ref dd = u.mk_day_of_epoch(ep);
        expr_ref one(a.mk_int(1), m);
        expr_ref mo_ge(a.mk_ge(mo, one), m);
        expr_ref mo_le(a.mk_le(mo, a.mk_int(12)), m);
        expr_ref dd_ge(a.mk_ge(dd, one), m);
        expr_ref dd_le(a.mk_le(dd, a.mk_int(31)), m);
        add_unit(mk_literal(mo_ge));
        add_unit(mk_literal(mo_le));
        add_unit(mk_literal(dd_ge));
        add_unit(mk_literal(dd_le));
    }

    /**
       \brief epoch(a) = epoch(b) => a = b
    */
    void solver::assert_injectivity(euf::enode* n1, euf::enode* n2) {
        expr_ref ep1(u.mk_epoch(n1->get_expr()), m);
        expr_ref ep2(u.mk_epoch(n2->get_expr()), m);
        sat::literal l_ep = eq_internalize(ep1, ep2);
        sat::literal l_d  = eq_internalize(n1->get_expr(), n2->get_expr());
        add_clause(~l_ep, l_d);
    }

    void solver::new_diseq_eh(euf::th_eq const& eq) {
        euf::enode* n1 = var2enode(eq.v1());
        euf::enode* n2 = var2enode(eq.v2());
        if (u.is_date(n1->get_expr()) && u.is_date(n2->get_expr()))
            assert_injectivity(n1, n2);
    }

    bool solver::epoch_value(euf::enode* n, rational& val) {
        arith::arith_value av(ctx);
        for (euf::enode* sib : euf::enode_class(n->get_root())) {
            expr* e = sib->get_expr();
            if (!u.is_date(e))
                continue;
            app_ref ep(u.mk_epoch(e), m);
            euf::enode* epn = expr2enode(ep);
            if (epn && av.get_value(ep, val) && val.is_int())
                return true;
        }
        return false;
    }

    sat::check_result solver::check() {
        force_push();
        vector<std::pair<rational, euf::enode*>> vals;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            euf::enode* n = var2enode(v);
            if (!u.is_date(n->get_expr()) || !n->is_root())
                continue;
            rational val(0);
            epoch_value(n, val);
            vals.push_back(std::make_pair(val, n));
        }
        std::sort(vals.begin(), vals.end(),
                  [](auto const& p1, auto const& p2) { return p1.first < p2.first; });
        bool ok = true;
        for (unsigned i = 0; i + 1 < vals.size(); ++i) {
            if (vals[i].first == vals[i + 1].first) {
                assert_injectivity(vals[i].second, vals[i + 1].second);
                ok = false;
            }
        }
        return ok ? sat::check_result::CR_DONE : sat::check_result::CR_CONTINUE;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(u.is_date(n->get_expr()));
        rational val(0);
        epoch_value(n, val);
        values.set(n->get_root_id(), u.mk_date_value(val));
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx, get_id());
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "theory date:\n";
        for (unsigned v = 0; v < get_num_vars(); ++v)
            out << v << ": " << mk_pp(var2enode(v)->get_expr(), m) << "\n";
        return out;
    }

}
