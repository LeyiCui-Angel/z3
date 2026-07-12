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

    void solver::assert_unit_axiom(expr* e) {
        expr_ref c(e, m);
        rewrite(c);
        if (m.is_true(c))
            return;
        add_unit(mk_literal(c));
    }

    void solver::internalize_date_op(app* t) {
        switch (t->get_decl_kind()) {
        case OP_DATE_MK: {
            expr* y = t->get_arg(0);
            expr* mo = t->get_arg(1);
            expr* d = t->get_arg(2);
            // strict constructor: the arguments must form a valid civil
            // date; formulas that force date.mk onto out-of-range
            // components are unsatisfiable
            assert_unit_axiom(a.mk_ge(mo, a.mk_int(1)));
            assert_unit_axiom(a.mk_le(mo, a.mk_int(12)));
            assert_unit_axiom(a.mk_ge(d, a.mk_int(1)));
            // bound-form atom (term <= numeral): the normal form the
            // arithmetic solvers expect for theory-created literals
            assert_unit_axiom(a.mk_le(a.mk_sub(d, u.mk_days_in_month(y, mo)), a.mk_int(0)));
            expr_ref ep(u.mk_epoch(t), m);
            assert_axiom_eq(ep, u.mk_days_from_civil(y, mo, d));
            // the components of the constructed date are the constructor
            // arguments. For ground constructors the definition above is
            // already a fixed epoch and the selector equalities are folded
            // by the rewriter wherever selectors occur.
            rational ry, rmo, rd;
            if (!u.is_numeral_mk(t, ry, rmo, rd)) {
                assert_axiom_eq(y, u.mk_year(t));
                assert_axiom_eq(mo, u.mk_month(t));
                assert_axiom_eq(d, u.mk_day(t));
            }
            // constructor-selector roundtrip fast-path
            if (u.is_year(y) && u.is_month(mo) && u.is_day(d)) {
                expr* x = to_app(y)->get_arg(0);
                if (x == to_app(mo)->get_arg(0) && x == to_app(d)->get_arg(0))
                    assert_axiom_eq(ep, u.mk_epoch(x));
            }
            break;
        }
        case OP_DATE_ADD:
        case OP_DATE_SUB: {
            // date.sub is date.add with negated offsets
            bool is_sub = t->get_decl_kind() == OP_DATE_SUB;
            expr* b = t->get_arg(0);
            expr_ref py(t->get_arg(1), m), pm(t->get_arg(2), m), pd(t->get_arg(3), m);
            if (is_sub) {
                py = u.mk_ineg(py);
                pm = u.mk_ineg(pm);
                pd = u.mk_ineg(pd);
            }
            if (u.is_zero_month_shift(py, pm)) {
                // pure day shift: the base date is a valid date, so the
                // month step and the day clamp are the identity and the
                // epoch shifts exactly
                expr_ref rhs(a.mk_add(u.mk_epoch(b), pd), m);
                assert_axiom_eq(u.mk_epoch(t), rhs);
            }
            else if (u.is_zero(pd)) {
                // pure month shift: the components of the result are
                // definable without division. On the absolute month
                // count 12*y + mo the shift is linear, and the bounds
                // 1 <= month <= 12 from the component axioms make the
                // year/month decomposition unique; the day is the base
                // day clamped to the target month length. The epoch
                // follows from the component axioms of the result
                // (asserted when the selector terms are internalized).
                assert_component_axioms(t);
                expr_ref yb(u.mk_year(b), m), mb(u.mk_month(b), m), db(u.mk_day(b), m);
                expr_ref yt(u.mk_year(t), m), mt(u.mk_month(t), m);
                expr_ref shift(a.mk_add(a.mk_mul(a.mk_int(12), py), pm), m);
                expr_ref rhs(a.mk_add(u.mk_month_total(yb, mb), shift), m);
                assert_axiom_eq(u.mk_month_total(yt, mt), rhs);
                expr_ref clamped = u.mk_clamped_day(db, yt, mt);
                assert_axiom_eq(u.mk_day(t), clamped);
            }
            else {
                // general shift: factor through the pure month shift,
                // then shift days exactly on epochs
                expr_ref zero(a.mk_int(0), m);
                expr* args[4] = { b, py, pm, zero };
                app_ref mid(m.mk_app(u.get_family_id(), OP_DATE_ADD, 4, args), m);
                expr_ref rhs(a.mk_add(u.mk_epoch(mid), pd), m);
                assert_axiom_eq(u.mk_epoch(t), rhs);
            }
            break;
        }
        case OP_DATE_YEAR:
        case OP_DATE_MONTH:
        case OP_DATE_DAY: {
            // the selector term itself is the component variable; for
            // date.mk arguments the constructor axioms already equate
            // the selectors with the arguments
            expr* b = t->get_arg(0);
            rational ry, rmo, rd;
            if (u.is_numeral_mk(b, ry, rmo, rd)) {
                // selectors of ground constructors are fixed (invalid
                // ground constructors force unsat through their own axioms)
                if (date_util::is_valid_civil(ry, rmo, rd)) {
                    rational v = t->get_decl_kind() == OP_DATE_YEAR ? ry :
                                 t->get_decl_kind() == OP_DATE_MONTH ? rmo : rd;
                    expr_ref val(a.mk_int(v), m);
                    assert_axiom_eq(t, val);
                }
            }
            else if (!u.is_mk(b))
                assert_component_axioms(b);
            break;
        }
        case OP_DATE_LT:
        case OP_DATE_LE:
        case OP_DATE_GT:
        case OP_DATE_GE: {
            expr_ref ep1(u.mk_epoch(t->get_arg(0)), m);
            expr_ref ep2(u.mk_epoch(t->get_arg(1)), m);
            // build bound-form atoms (term <= numeral): this is the normal
            // form the arithmetic solvers expect for theory-created literals
            expr_ref ineq(m);
            switch (t->get_decl_kind()) {
            case OP_DATE_LT: ineq = a.mk_le(a.mk_sub(ep1, ep2), a.mk_int(-1)); break;
            case OP_DATE_LE: ineq = a.mk_le(a.mk_sub(ep1, ep2), a.mk_int(0)); break;
            case OP_DATE_GT: ineq = a.mk_le(a.mk_sub(ep2, ep1), a.mk_int(-1)); break;
            case OP_DATE_GE: ineq = a.mk_le(a.mk_sub(ep2, ep1), a.mk_int(0)); break;
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
       \brief Component axioms for a Date term: its selector terms form a
       valid civil triple whose days-from-civil image is its epoch. The
       selectors act as the component variables of the relational
       encoding; the inverse civil-of-epoch direction is never encoded,
       the integer solver searches over the bounded components instead.
    */
    void solver::assert_component_axioms(expr* d) {
        expr_ref y(u.mk_year(d), m);
        expr_ref mo(u.mk_month(d), m);
        expr_ref dd(u.mk_day(d), m);
        assert_unit_axiom(a.mk_ge(mo, a.mk_int(1)));
        assert_unit_axiom(a.mk_le(mo, a.mk_int(12)));
        assert_unit_axiom(a.mk_ge(dd, a.mk_int(1)));
        // bound form (term <= numeral): days-in-month is an ite term
        assert_unit_axiom(a.mk_le(a.mk_sub(dd, u.mk_days_in_month(y, mo)), a.mk_int(0)));
        expr_ref ep(u.mk_epoch(d), m);
        assert_axiom_eq(ep, u.mk_days_from_civil(y, mo, dd));
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

    /**
       \brief Components of dates are uniquely determined, so equal dates
       built by date.mk have equal constructor arguments. This gives the
       arithmetic solver the component equalities directly instead of
       requiring it to invert the days-from-civil map.
    */
    void solver::assert_mk_injectivity(euf::enode* n) {
        euf::enode* pivot = nullptr;
        for (euf::enode* sib : euf::enode_class(n->get_root())) {
            expr* s = sib->get_expr();
            if (!u.is_mk(s))
                continue;
            if (!pivot) {
                pivot = sib;
                continue;
            }
            expr* p = pivot->get_expr();
            sat::literal l_eq = eq_internalize(p, s);
            for (unsigned i = 0; i < 3; ++i)
                add_clause(~l_eq, eq_internalize(to_app(p)->get_arg(i), to_app(s)->get_arg(i)));
        }
    }

    /**
       \brief When two epoch terms merge (through congruence, unit axioms,
       or equalities proposed by the arithmetic solver's model-based theory
       combination), force the underlying dates to merge as well. When two
       date terms merge, propagate equalities between the arguments of
       date.mk terms in the merged class.
    */
    void solver::new_eq_eh(euf::th_eq const& eq) {
        euf::enode* n1 = var2enode(eq.v1());
        euf::enode* n2 = var2enode(eq.v2());
        expr* e1 = n1->get_expr();
        expr* e2 = n2->get_expr();
        if (u.is_date(e1) && u.is_date(e2)) {
            assert_mk_injectivity(n1);
            return;
        }
        if (!u.is_epoch(e1) || !u.is_epoch(e2))
            return;
        euf::enode* d1 = expr2enode(to_app(e1)->get_arg(0));
        euf::enode* d2 = expr2enode(to_app(e2)->get_arg(0));
        if (d1 && d2 && d1->get_root() != d2->get_root())
            assert_injectivity(d1, d2);
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
        // injectivity is enforced through new_eq_eh: epoch terms are shared
        // with the arithmetic solver, whose model-based theory combination
        // proposes equalities between equal-valued epochs.
        return sat::check_result::CR_DONE;
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
