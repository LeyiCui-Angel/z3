/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates in the SAT/EUF pipeline.

Author:

    Claude 2026-07-04

--*/
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"

namespace date {

    static params_ref date_rewriter_params() {
        params_ref p;
        // the arithmetic solver expects atoms in bound normal form t <= c
        p.set_bool("arith_lhs", true);
        return p;
    }

    solver::solver(euf::solver& ctx, euf::theory_id id) :
        th_euf_solver(ctx, ctx.get_manager().get_family_name(id), id),
        u(ctx.get_manager()),
        m_rw(ctx.get_manager(), date_rewriter_params()) {
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx, get_id());
    }

    void solver::add_axiom_unit(expr* e) {
        expr_ref r(e, m);
        m_rw(r);
        if (m.is_true(r))
            return;
        add_unit(mk_literal(r));
    }

    void solver::add_axiom_unit_raw(expr* e) {
        expr_ref r(e, m);
        add_unit(mk_literal(r));
    }

    /**
       Assert for the Date term of n:
       - validity of the selector triple, and
       - the reconstruction x = date.mk(year x, month x, day x),
         skipped on date.mk applications where the (guarded) selector
         equations subsume it and asserting it would loop.
    */
    void solver::add_date_axioms(euf::enode* n) {
        expr* x = n->get_expr();
        arith_util& a = u.arith();
        app_ref y(u.mk_year(x), m), mo(u.mk_month(x), m), d(u.mk_day(x), m);
        add_axiom_unit(a.mk_le(a.mk_int(1), mo));
        add_axiom_unit(a.mk_le(mo, a.mk_int(12)));
        add_axiom_unit(a.mk_le(a.mk_int(1), d));
        add_axiom_unit(a.mk_le(d, u.mk_days_in_month_expr(y, mo)));
        add_axiom_unit(m.mk_eq(u.mk_rata(x), u.mk_rata_die_expr(y, mo, d)));
        if (!u.is_mk(x))
            add_axiom_unit(m.mk_eq(x, u.mk_mk(y, mo, d)));
    }

    /**
       For t = (date.mk y m d) assert the selector equations guarded by
       calendar validity of the argument triple; invalid constructor
       applications denote an unspecified valid date.
    */
    void solver::add_mk_axioms(app* t) {
        expr* y = t->get_arg(0);
        expr* mo = t->get_arg(1);
        expr* d = t->get_arg(2);
        arith_util& a = u.arith();
        rational ry, rm, rd;
        if (u.is_value_mk(t, ry, rm, rd)) {
            // keep the selector terms of concrete dates in the e-graph
            // (unsimplified) so that congruence links them to the selectors
            // of terms the date is equated with
            add_axiom_unit_raw(m.mk_eq(u.mk_year(t), a.mk_int(ry)));
            add_axiom_unit_raw(m.mk_eq(u.mk_month(t), a.mk_int(rm)));
            add_axiom_unit_raw(m.mk_eq(u.mk_day(t), a.mk_int(rd)));
            add_axiom_unit_raw(m.mk_eq(u.mk_rata(t), a.mk_int(date_util::rata_die(ry, rm, rd))));
            return;
        }
        expr_ref valid(u.mk_valid_expr(y, mo, d), m);
        m_rw(valid);
        if (m.is_false(valid))
            return;
        expr_ref ye(m.mk_eq(u.mk_year(t), y), m);
        expr_ref me(m.mk_eq(u.mk_month(t), mo), m);
        expr_ref de(m.mk_eq(u.mk_day(t), d), m);
        m_rw(ye);
        m_rw(me);
        m_rw(de);
        if (m.is_true(valid)) {
            add_axiom_unit(ye);
            add_axiom_unit(me);
            add_axiom_unit(de);
            return;
        }
        sat::literal lv = mk_literal(valid);
        for (expr* e : { ye.get(), me.get(), de.get() })
            if (!m.is_true(e))
                add_clause(~lv, mk_literal(e));
    }

    /**
       For t = (date.add x py pm pd), let (oy, om, od) be the month
       normalization and end-of-month clamp of x by (py, pm). The triple is
       calendar-valid by construction and is materialized as the internal
       constructor term mkc = (date.mk oy om od); the day carry becomes

           date.rata(t) = date.rata(mkc) + pd.

       date.sub is handled as date.add with negated period arguments.
    */
    void solver::add_arith_axioms(app* t) {
        expr* x = t->get_arg(0);
        expr_ref py(t->get_arg(1), m), pm(t->get_arg(2), m), pd(t->get_arg(3), m);
        arith_util& a = u.arith();
        if (u.is_sub(t)) {
            py = a.mk_uminus(py);
            pm = a.mk_uminus(pm);
            pd = a.mk_uminus(pd);
        }
        expr_ref oy(m), om(m), od(m);
        u.mk_add_normalize_exprs(u.mk_year(x), u.mk_month(x), u.mk_day(x), py, pm, oy, om, od);
        m_rw(oy);
        m_rw(om);
        m_rw(od);
        app_ref mkc(u.mk_mk(oy, om, od), m);
        add_axiom_unit(m.mk_eq(u.mk_year(mkc), oy));
        add_axiom_unit(m.mk_eq(u.mk_month(mkc), om));
        add_axiom_unit(m.mk_eq(u.mk_day(mkc), od));
        rational vd;
        if (a.is_numeral(pd, vd) && vd.is_zero())
            // a zero day carry makes the result the clamped date itself
            add_axiom_unit(m.mk_eq(t, mkc));
        add_axiom_unit(m.mk_eq(u.mk_rata(t), a.mk_add(u.mk_rata(mkc), pd)));
    }

    /**
       Comparison atoms become integer comparisons of day numbers, which
       agree with the lexicographic order on (year, month, day) for
       calendar-valid dates.
    */
    void solver::add_cmp_axioms(sat::literal lit, app* atom) {
        expr_ref r1(u.mk_rata(atom->get_arg(0)), m);
        expr_ref r2(u.mk_rata(atom->get_arg(1)), m);
        arith_util& a = u.arith();
        expr_ref cmp(m);
        switch (atom->get_decl_kind()) {
        case OP_DATE_LT: cmp = a.mk_lt(r1, r2); break;
        case OP_DATE_LE: cmp = a.mk_le(r1, r2); break;
        case OP_DATE_GT: cmp = a.mk_lt(r2, r1); break;
        case OP_DATE_GE: cmp = a.mk_le(r2, r1); break;
        default: UNREACHABLE();
        }
        m_rw(cmp);
        sat::literal l = mk_literal(cmp);
        add_clause(~lit, l);
        add_clause(lit, ~l);
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        euf::theory_var v = th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, v);
        if (u.is_date(n->get_expr())) {
            add_date_axioms(n);
            add_injectivity_axioms(n->get_expr(), v);
        }
        return v;
    }

    /**
       The day-number map is injective on calendar-valid dates: dates with
       equal day numbers are equal. Instantiated pairwise so that equality
       of dates follows from day-number reasoning without inverting the
       day-number function arithmetically.
    */
    void solver::add_injectivity_axioms(expr* x, euf::theory_var v) {
        for (euf::theory_var w = 0; w < v; ++w) {
            expr* xw = var2expr(w);
            if (!u.is_date(xw))
                continue;
            expr_ref req(m.mk_eq(u.mk_rata(x), u.mk_rata(xw)), m);
            m_rw(req);
            if (m.is_false(req))
                continue;
            sat::literal deq = eq_internalize(x, xw);
            if (m.is_true(req)) {
                add_unit(deq);
                continue;
            }
            add_clause(~mk_literal(req), deq);
        }
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        sat::literal lit = ctx.expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e) {
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
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n)
            n = mk_enode(e, false);
        mk_var(n);
        app* t = to_app(e);
        switch (t->get_decl_kind()) {
        case OP_DATE_MK:
            add_mk_axioms(t);
            break;
        case OP_DATE_ADD:
        case OP_DATE_SUB:
            add_arith_axioms(t);
            break;
        case OP_DATE_YEAR:
        case OP_DATE_MONTH:
        case OP_DATE_DAY:
        case OP_DATE_RATA:
            mk_var(expr2enode(t->get_arg(0)));
            break;
        case OP_DATE_LT:
        case OP_DATE_LE:
        case OP_DATE_GT:
        case OP_DATE_GE:
            add_cmp_axioms(expr2literal(e), t);
            break;
        default:
            break;
        }
        return true;
    }

    void solver::apply_sort_cnstr(euf::enode* n, sort* s) {
        SASSERT(u.is_date(s));
        mk_var(n);
    }

    euf::enode* solver::selector_enode(euf::enode* n, decl_kind k) const {
        expr_ref e(m.mk_app(get_id(), k, n->get_expr()), m);
        return expr2enode(e);
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (!u.is_date(n->get_expr()))
            return false;
        rational y, mo, d;
        for (euf::enode* k : euf::enode_class(n->get_root()))
            if (u.is_value_mk(k->get_expr(), y, mo, d)) {
                dep.insert(n, nullptr);
                return true;
            }
        euf::enode* ye = selector_enode(n, OP_DATE_YEAR);
        euf::enode* me = selector_enode(n, OP_DATE_MONTH);
        euf::enode* de = selector_enode(n, OP_DATE_DAY);
        if (ye && me && de) {
            dep.add(n, ye);
            dep.add(n, me);
            dep.add(n, de);
        }
        else
            dep.insert(n, nullptr);
        return true;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        arith_util& a = u.arith();
        rational y, mo, d;
        for (euf::enode* k : euf::enode_class(n->get_root()))
            if (u.is_value_mk(k->get_expr(), y, mo, d)) {
                values.set(n->get_root_id(), k->get_expr());
                return;
            }
        euf::enode* ye = selector_enode(n, OP_DATE_YEAR);
        euf::enode* me = selector_enode(n, OP_DATE_MONTH);
        euf::enode* de = selector_enode(n, OP_DATE_DAY);
        if (ye && me && de &&
            a.is_numeral(values.get(ye->get_root_id(), nullptr), y) &&
            a.is_numeral(values.get(me->get_root_id(), nullptr), mo) &&
            a.is_numeral(values.get(de->get_root_id(), nullptr), d) &&
            date_util::is_valid_date(y, mo, d)) {
            values.set(n->get_root_id(), u.mk_date_value(y, mo, d));
            return;
        }
        // no constraints reached this date term; any valid date will do
        values.set(n->get_root_id(), u.mk_date_value(rational(1), rational(1), rational(1)));
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out << "theory date\n";
    }
}
