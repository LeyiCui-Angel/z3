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
        m_rw(ctx.get_manager(), date_rewriter_params()),
        m_internal_pinned(ctx.get_manager()) {
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
        if (!u.is_mk(x))
            add_axiom_unit(m.mk_eq(x, u.mk_mk(y, mo, d)));
        rational ry, rm, rd;
        if (!u.is_numeral_mk(x, ry, rm, rd)) {
            // bias the search toward calendar-realistic years so that weakly
            // constrained dates receive small model values. The disjunction
            // of the two bounds is a tautology on the integers, so asserting
            // it never changes satisfiability; it merely places the bound
            // atoms in a clause so that they are decided, and the true-first
            // phase makes the SAT engine try the [1, 9999] box before
            // resorting to out-of-range years.
            sat::literal lo = mk_literal(a.mk_le(a.mk_int(1), y));
            sat::literal hi = mk_literal(a.mk_le(y, a.mk_int(9999)));
            add_clause(lo, hi);
            m_bias_vars.insert(lo.var());
            m_bias_vars.insert(hi.var());
        }
    }

    /**
       Define the day number of the Date term x through its selector
       triple: date.rata(x) = rata_die(year x, month x, day x). Asserted
       lazily, only for dates whose day number actually participates in
       constraints (date.add/date.sub day carry); comparisons and equality
       are handled on the selectors and never need it.
    */
    void solver::ensure_rata_def(expr* x) {
        if (m_rata_defined.contains(x))
            return;
        m_rata_defined.insert(x);
        m_internal_pinned.push_back(x);
        arith_util& a = u.arith();
        rational ry, rm, rd;
        if (u.is_numeral_mk(x, ry, rm, rd)) {
            if (!date_util::is_valid_date(ry, rm, rd))
                date_util::normalize_mk(ry, rm, rd);
            add_axiom_unit_raw(m.mk_eq(u.mk_rata(x), a.mk_int(date_util::rata_die(ry, rm, rd))));
        }
        else
            add_axiom_unit(m.mk_eq(u.mk_rata(x),
                                   u.mk_rata_die_expr(u.mk_year(x), u.mk_month(x), u.mk_day(x))));
        // the day-number map is injective on calendar-valid dates: equal day
        // numbers imply equal dates. Instantiated pairwise among the dates
        // whose day number is defined, so that date equalities forced by
        // day-number arithmetic (e.g. add/sub round trips) propagate without
        // inverting the day-number function.
        for (expr* w : m_rata_dates) {
            expr_ref req(m.mk_eq(u.mk_rata(x), u.mk_rata(w)), m);
            m_rw(req);
            if (m.is_false(req))
                continue;
            sat::literal deq = eq_internalize(x, w);
            if (m.is_true(req)) {
                add_unit(deq);
                continue;
            }
            add_clause(~mk_literal(req), deq);
        }
        m_rata_dates.push_back(x);
    }

    /**
       For t = (date.mk y m d):
       - numeral triples denote a concrete date: invalid triples fold to the
         fixed total interpretation (date_util::normalize_mk), matching the
         rewriter, and the selector equations are asserted unconditionally;
       - symbolic constructor applications carry the implicit validity
         obligation of the theory: valid(y, m, d) is asserted together with
         the (now unconditional) selector equations. A symbolic date.mk with
         arguments that cannot form a calendar-valid date is unsatisfiable.
    */
    void solver::add_mk_axioms(app* t) {
        expr* y = t->get_arg(0);
        expr* mo = t->get_arg(1);
        expr* d = t->get_arg(2);
        arith_util& a = u.arith();
        rational ry, rm, rd;
        if (u.is_numeral_mk(t, ry, rm, rd)) {
            if (!date_util::is_valid_date(ry, rm, rd))
                // direct invalid application: fixed total interpretation
                date_util::normalize_mk(ry, rm, rd);
            // keep the selector terms of concrete dates in the e-graph
            // (unsimplified) so that congruence links them to the selectors
            // of terms the date is equated with
            add_axiom_unit_raw(m.mk_eq(u.mk_year(t), a.mk_int(ry)));
            add_axiom_unit_raw(m.mk_eq(u.mk_month(t), a.mk_int(rm)));
            add_axiom_unit_raw(m.mk_eq(u.mk_day(t), a.mk_int(rd)));
            return;
        }
        // implicit validity obligation on symbolic date.mk arguments.
        // Internal constructor terms (add_arith_axioms) are exempt: their
        // arguments are calendar-valid by construction and the obligation
        // would only burden the arithmetic solver with redundant constraints.
        if (!m_internal_mk.contains(t))
            add_axiom_unit(u.mk_valid_expr(y, mo, d));
        add_axiom_unit(m.mk_eq(u.mk_year(t), y));
        add_axiom_unit(m.mk_eq(u.mk_month(t), mo));
        add_axiom_unit(m.mk_eq(u.mk_day(t), d));
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
        if (!m_internal_mk.contains(mkc)) {
            m_internal_mk.insert(mkc);
            m_internal_pinned.push_back(mkc);
        }
        add_axiom_unit(m.mk_eq(u.mk_year(mkc), oy));
        add_axiom_unit(m.mk_eq(u.mk_month(mkc), om));
        add_axiom_unit(m.mk_eq(u.mk_day(mkc), od));
        rational vd;
        if (a.is_numeral(pd, vd) && vd.is_zero()) {
            // a zero day carry makes the result the clamped date itself
            add_axiom_unit(m.mk_eq(t, mkc));
            return;
        }
        // day carry through the day-number bijection; requires the day
        // numbers of the clamped date and of the result to be defined
        ensure_rata_def(mkc);
        ensure_rata_def(t);
        add_axiom_unit(m.mk_eq(u.mk_rata(t), a.mk_add(u.mk_rata(mkc), pd)));
    }

    /**
       Comparison atoms are mapped to the lexicographic order on the
       selector triples (year, month, day). The encoding is linear, so
       comparisons never involve the day-number function.
    */
    void solver::add_cmp_axioms(sat::literal lit, app* atom) {
        expr* x1 = atom->get_arg(0);
        expr* x2 = atom->get_arg(1);
        app_ref y1(u.mk_year(x1), m), m1(u.mk_month(x1), m), d1(u.mk_day(x1), m);
        app_ref y2(u.mk_year(x2), m), m2(u.mk_month(x2), m), d2(u.mk_day(x2), m);
        expr_ref cmp(m);
        switch (atom->get_decl_kind()) {
        case OP_DATE_LT: cmp = u.mk_lex_cmp_expr(true, y1, m1, d1, y2, m2, d2); break;
        case OP_DATE_LE: cmp = u.mk_lex_cmp_expr(false, y1, m1, d1, y2, m2, d2); break;
        case OP_DATE_GT: cmp = u.mk_lex_cmp_expr(true, y2, m2, d2, y1, m1, d1); break;
        case OP_DATE_GE: cmp = u.mk_lex_cmp_expr(false, y2, m2, d2, y1, m1, d1); break;
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
       The selector triple determines the date: dates with equal
       (year, month, day) are equal. Instantiated pairwise so that
       equality of dates follows from linear selector reasoning.
    */
    void solver::add_injectivity_axioms(expr* x, euf::theory_var v) {
        for (euf::theory_var w = 0; w < v; ++w) {
            expr* xw = var2expr(w);
            if (!u.is_date(xw))
                continue;
            expr_ref ey(m.mk_eq(u.mk_year(x), u.mk_year(xw)), m);
            expr_ref em(m.mk_eq(u.mk_month(x), u.mk_month(xw)), m);
            expr_ref ed(m.mk_eq(u.mk_day(x), u.mk_day(xw)), m);
            m_rw(ey);
            m_rw(em);
            m_rw(ed);
            if (m.is_false(ey) || m.is_false(em) || m.is_false(ed))
                continue;
            sat::literal deq = eq_internalize(x, xw);
            sat::literal_vector lits;
            for (expr* e : { ey.get(), em.get(), ed.get() })
                if (!m.is_true(e))
                    lits.push_back(~mk_literal(e));
            lits.push_back(deq);
            add_clause(lits);
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
            mk_var(expr2enode(t->get_arg(0)));
            break;
        case OP_DATE_RATA:
            mk_var(expr2enode(t->get_arg(0)));
            // any internalized day-number term must be defined through the
            // selector triple of its argument
            ensure_rata_def(t->get_arg(0));
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

    /**
       Decision-phase override for the year-range bias variables: the
       arithmetic solver's phase heuristic evaluates bound atoms under its
       current (often out-of-range) assignment, which would steer years away
       from the preferred box. Answering the phase here takes precedence.
    */
    bool solver::decide(sat::bool_var& var, lbool& phase) {
        if (!m_bias_vars.contains(var))
            return false;
        phase = l_true;
        return true;
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out << "theory date\n";
    }
}
