/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Theory plugin for calendar dates.

Author:

    Claude 2026-07-04

--*/
#include "smt/smt_context.h"
#include "smt/theory_date.h"
#include "smt/smt_model_generator.h"
#include "model/date_factory.h"
#include "ast/ast_pp.h"

namespace smt {

    static params_ref date_rewriter_params() {
        params_ref p;
        // the arithmetic solver expects atoms in bound normal form t <= c
        p.set_bool("arith_lhs", true);
        return p;
    }

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        u(ctx.get_manager()),
        m_rw(ctx.get_manager(), date_rewriter_params()),
        m_pinned(ctx.get_manager()) {
    }

    theory_var theory_date::mk_th_var(enode* n) {
        theory_var v = theory::mk_var(n);
        ctx.attach_th_var(n, this, v);
        return v;
    }

    void theory_date::assert_axiom(expr* e) {
        expr_ref r(e, m);
        m_rw(r);
        if (m.is_true(r))
            return;
        assert_axiom_raw(r);
    }

    void theory_date::assert_axiom_raw(expr* e) {
        literal l = mk_literal(e);
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), 1, &l);
    }

    /**
       Attach a theory variable to the Date term of n and assert:
       - validity: the selector triple (date.year x, date.month x, date.day x)
         denotes a calendar-valid Gregorian date;
       - reconstruction: x = (date.mk (date.year x) (date.month x) (date.day x)).
       Reconstruction is skipped for date.mk terms; for those the (guarded)
       selector equations added by add_mk_axioms subsume it, and asserting it
       on constructor applications would loop.
    */
    void theory_date::ensure_date_axioms(enode* n) {
        if (is_attached_to_var(n))
            return;
        theory_var v = mk_th_var(n);
        expr* x = n->get_expr();
        arith_util& a = u.arith();
        app_ref y(u.mk_year(x), m), mo(u.mk_month(x), m), d(u.mk_day(x), m);
        m_pinned.push_back(y);
        m_pinned.push_back(mo);
        m_pinned.push_back(d);
        m_year.setx(v, y, nullptr);
        m_month.setx(v, mo, nullptr);
        m_day.setx(v, d, nullptr);
        assert_axiom(a.mk_le(a.mk_int(1), mo));
        assert_axiom(a.mk_le(mo, a.mk_int(12)));
        assert_axiom(a.mk_le(a.mk_int(1), d));
        assert_axiom(a.mk_le(d, u.mk_days_in_month_expr(y, mo)));
        rational ry, rm, rd;
        if (!u.is_numeral_mk(x, ry, rm, rd)) {
            // bias the search toward calendar-realistic years so that weakly
            // constrained dates receive small model values. The two bounds
            // are only preferred decision literals, never asserted: if the
            // constraints force a year outside [1, 9999] the SAT engine
            // simply flips them.
            literal lo = mk_literal(a.mk_le(a.mk_int(1), y));
            literal hi = mk_literal(a.mk_le(y, a.mk_int(9999)));
            ctx.mark_as_relevant(lo);
            ctx.mark_as_relevant(hi);
            ctx.set_true_first_flag(lo.var());
            ctx.set_true_first_flag(hi.var());
        }
        if (!u.is_mk(x))
            assert_axiom(m.mk_eq(x, u.mk_mk(y, mo, d)));
        // the selector triple determines the date: dates with equal
        // (year, month, day) are equal. Instantiated pairwise so that
        // equality of dates follows from linear selector reasoning.
        for (theory_var w = 0; w < v; ++w) {
            expr* xw = get_enode(w)->get_expr();
            expr_ref ey(m.mk_eq(y, year_of(w)), m);
            expr_ref em(m.mk_eq(mo, month_of(w)), m);
            expr_ref ed(m.mk_eq(d, day_of(w)), m);
            m_rw(ey);
            m_rw(em);
            m_rw(ed);
            if (m.is_false(ey) || m.is_false(em) || m.is_false(ed))
                continue;
            literal deq = mk_eq(x, xw, false);
            ctx.mark_as_relevant(deq);
            literal_vector lits;
            for (expr* e : { ey.get(), em.get(), ed.get() }) {
                if (m.is_true(e))
                    continue;
                literal l = mk_literal(e);
                ctx.mark_as_relevant(l);
                lits.push_back(~l);
            }
            lits.push_back(deq);
            ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
        }
    }

    /**
       Define the day number of the Date term x through its selector
       triple: date.rata(x) = rata_die(year x, month x, day x). Asserted
       lazily, only for dates whose day number actually participates in
       constraints (date.add/date.sub day carry); comparisons and equality
       are handled on the selectors and never need it.
    */
    void theory_date::ensure_rata_def(expr* x) {
        if (m_rata_defined.contains(x))
            return;
        m_rata_defined.insert(x);
        m_pinned.push_back(x);
        arith_util& a = u.arith();
        rational ry, rm, rd;
        if (u.is_numeral_mk(x, ry, rm, rd)) {
            if (!date_util::is_valid_date(ry, rm, rd))
                date_util::normalize_mk(ry, rm, rd);
            assert_axiom_raw(m.mk_eq(u.mk_rata(x), a.mk_int(date_util::rata_die(ry, rm, rd))));
        }
        else
            assert_axiom(m.mk_eq(u.mk_rata(x),
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
            literal deq = mk_eq(x, w, false);
            ctx.mark_as_relevant(deq);
            if (m.is_true(req)) {
                ctx.mk_th_axiom(get_id(), 1, &deq);
                continue;
            }
            literal leq = mk_literal(req);
            ctx.mark_as_relevant(leq);
            ctx.mk_th_axiom(get_id(), ~leq, deq);
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
    void theory_date::add_mk_axioms(app* t) {
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
            assert_axiom_raw(m.mk_eq(u.mk_year(t), a.mk_int(ry)));
            assert_axiom_raw(m.mk_eq(u.mk_month(t), a.mk_int(rm)));
            assert_axiom_raw(m.mk_eq(u.mk_day(t), a.mk_int(rd)));
            return;
        }
        // implicit validity obligation on symbolic date.mk arguments.
        // Internal constructor terms (add_arith_axioms) are exempt: their
        // arguments are calendar-valid by construction and the obligation
        // would only burden the arithmetic solver with redundant constraints.
        if (!m_internal_mk.contains(t))
            assert_axiom(u.mk_valid_expr(y, mo, d));
        assert_axiom(m.mk_eq(u.mk_year(t), y));
        assert_axiom(m.mk_eq(u.mk_month(t), mo));
        assert_axiom(m.mk_eq(u.mk_day(t), d));
    }

    /**
       For t = (date.add x py pm pd), let (oy, om, od) be the month
       normalization and end-of-month clamp of x by (py, pm) (steps 1 and 2
       of the date.add algorithm). The triple (oy, om, od) is calendar-valid
       by construction, and it is materialized as the internal constructor
       term mkc = (date.mk oy om od) with unconditional selector equations.
       Step 3 (day carry) becomes the day-number equation

           date.rata(t) = date.rata(mkc) + pd

       which, together with the per-term day-number definitions and the
       validity axioms of t, pins down exactly one result date.
       date.sub is handled as date.add with negated period arguments.
    */
    void theory_date::add_arith_axioms(app* t) {
        expr* x = t->get_arg(0);
        expr_ref py(t->get_arg(1), m), pm(t->get_arg(2), m), pd(t->get_arg(3), m);
        arith_util& a = u.arith();
        if (u.is_sub(t)) {
            py = a.mk_uminus(py);
            pm = a.mk_uminus(pm);
            pd = a.mk_uminus(pd);
        }
        ensure_date_axioms(ctx.get_enode(x));
        ensure_date_axioms(ctx.get_enode(t));
        expr_ref oy(m), om(m), od(m);
        u.mk_add_normalize_exprs(u.mk_year(x), u.mk_month(x), u.mk_day(x), py, pm, oy, om, od);
        m_rw(oy);
        m_rw(om);
        m_rw(od);
        app_ref mkc(u.mk_mk(oy, om, od), m);
        if (!m_internal_mk.contains(mkc)) {
            m_internal_mk.insert(mkc);
            m_pinned.push_back(mkc);
        }
        assert_axiom(m.mk_eq(u.mk_year(mkc), oy));
        assert_axiom(m.mk_eq(u.mk_month(mkc), om));
        assert_axiom(m.mk_eq(u.mk_day(mkc), od));
        rational vd;
        if (a.is_numeral(pd, vd) && vd.is_zero()) {
            // a zero day carry makes the result the clamped date itself
            assert_axiom(m.mk_eq(t, mkc));
            return;
        }
        // day carry through the day-number bijection; requires the day
        // numbers of the clamped date and of the result to be defined
        ensure_rata_def(mkc);
        ensure_rata_def(t);
        assert_axiom(m.mk_eq(u.mk_rata(t), a.mk_add(u.mk_rata(mkc), pd)));
    }

    /**
       Comparison atoms are mapped to the lexicographic order on the
       selector triples (year, month, day). The encoding is linear, so
       comparisons never involve the day-number function.
    */
    void theory_date::add_cmp_axioms(literal lit, app* atom) {
        expr* x1 = atom->get_arg(0);
        expr* x2 = atom->get_arg(1);
        ensure_date_axioms(ctx.get_enode(x1));
        ensure_date_axioms(ctx.get_enode(x2));
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
        literal l = mk_literal(cmp);
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), ~lit, l);
        ctx.mk_th_axiom(get_id(), lit, ~l);
    }

    void theory_date::push_scope_eh() {
        theory::push_scope_eh();
        m_rata_lim.push_back(m_rata_dates.size());
    }

    void theory_date::pop_scope_eh(unsigned num_scopes) {
        unsigned old_sz = m_rata_lim[m_rata_lim.size() - num_scopes];
        for (unsigned i = old_sz; i < m_rata_dates.size(); ++i)
            m_rata_defined.erase(m_rata_dates[i]);
        m_rata_dates.shrink(old_sz);
        m_rata_lim.shrink(m_rata_lim.size() - num_scopes);
        theory::pop_scope_eh(num_scopes);
    }

    bool theory_date::internalize_atom(app * atom, bool gate_ctx) {
        SASSERT(u.is_lt(atom) || u.is_le(atom) || u.is_gt(atom) || u.is_ge(atom));
        for (expr* arg : *atom)
            ctx.internalize(arg, false);
        if (ctx.b_internalized(atom))
            return true;
        bool_var bv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(bv, get_id());
        add_cmp_axioms(literal(bv), atom);
        return true;
    }

    bool theory_date::internalize_term(app * term) {
        for (expr* arg : *term)
            ctx.internalize(arg, false);
        if (!ctx.e_internalized(term))
            ctx.mk_enode(term, false, false, true);
        enode* e = ctx.get_enode(term);
        if (u.is_date(term))
            ensure_date_axioms(e);
        switch (term->get_decl_kind()) {
        case OP_DATE_MK:
            add_mk_axioms(term);
            break;
        case OP_DATE_ADD:
        case OP_DATE_SUB:
            add_arith_axioms(term);
            break;
        case OP_DATE_YEAR:
        case OP_DATE_MONTH:
        case OP_DATE_DAY:
            ensure_date_axioms(ctx.get_enode(term->get_arg(0)));
            break;
        case OP_DATE_RATA:
            ensure_date_axioms(ctx.get_enode(term->get_arg(0)));
            // any internalized day-number term must be defined through the
            // selector triple of its argument
            ensure_rata_def(term->get_arg(0));
            break;
        default:
            break;
        }
        return true;
    }

    void theory_date::apply_sort_cnstr(enode * n, sort * s) {
        SASSERT(u.is_date(s));
        ensure_date_axioms(n);
    }

    void theory_date::init_model(model_generator & mg) {
        mg.register_factory(alloc(date_factory, m, get_family_id()));
    }

    /**
       The model value of a Date term is (date.mk y m d) where y, m, d are
       the arithmetic model values of its selector terms.
    */
    class date_value_proc : public model_value_proc {
        date_util& u;
        enode*     m_year;
        enode*     m_month;
        enode*     m_day;
    public:
        date_value_proc(date_util& u, enode* y, enode* mo, enode* d):
            u(u), m_year(y), m_month(mo), m_day(d) {}
        void get_dependencies(buffer<model_value_dependency> & result) override {
            result.push_back(model_value_dependency(m_year));
            result.push_back(model_value_dependency(m_month));
            result.push_back(model_value_dependency(m_day));
        }
        app * mk_value(model_generator & mg, expr_ref_vector const & values) override {
            SASSERT(values.size() == 3);
            arith_util& a = u.arith();
            rational y, mo, d;
            if (a.is_numeral(values[0], y) && a.is_numeral(values[1], mo) && a.is_numeral(values[2], d) &&
                date_util::is_valid_date(y, mo, d))
                return u.mk_date_value(y, mo, d);
            // selector values must form a valid date by the theory axioms;
            // be defensive if arithmetic left them unassigned
            return u.mk_date_value(rational(1), rational(1), rational(1));
        }
    };

    model_value_proc * theory_date::mk_value(enode * n, model_generator & mg) {
        enode* r = n->get_root();
        rational y, mo, d;
        // if the class already contains a concrete date, use it directly
        for (enode* k : *r)
            if (u.is_value_mk(k->get_expr(), y, mo, d))
                return alloc(expr_wrapper_proc, to_app(k->get_expr()));
        theory_var v = r->get_th_var(get_id());
        SASSERT(v != null_theory_var);
        app* ye = year_of(v), *me = month_of(v), *de = day_of(v);
        if (ye && ctx.e_internalized(ye) && ctx.e_internalized(me) && ctx.e_internalized(de))
            return alloc(date_value_proc, u, ctx.get_enode(ye), ctx.get_enode(me), ctx.get_enode(de));
        // the axioms folded to concrete facts and left no symbolic selectors;
        // any valid date is consistent with the empty constraint set
        return alloc(expr_wrapper_proc, u.mk_date_value(rational(1), rational(1), rational(1)));
    }

    void theory_date::display(std::ostream & out) const {
        out << "theory date:\n";
        for (unsigned v = 0; v < get_num_vars(); ++v)
            out << v << ": " << mk_pp(get_enode(v)->get_expr(), m) << "\n";
    }

}
