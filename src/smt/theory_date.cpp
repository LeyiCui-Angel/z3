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
        m_rw(ctx.get_manager(), date_rewriter_params()) {
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
        literal l = mk_literal(r);
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
        m_year.setx(v, y, nullptr);
        m_month.setx(v, mo, nullptr);
        m_day.setx(v, d, nullptr);
        assert_axiom(a.mk_le(a.mk_int(1), mo));
        assert_axiom(a.mk_le(mo, a.mk_int(12)));
        assert_axiom(a.mk_le(a.mk_int(1), d));
        assert_axiom(a.mk_le(d, u.mk_days_in_month_expr(y, mo)));
        if (!u.is_mk(x))
            assert_axiom(m.mk_eq(x, u.mk_mk(y, mo, d)));
    }

    /**
       For t = (date.mk y m d) assert the selector equations guarded by
       calendar validity of (y, m, d):
           valid(y, m, d) => date.year(t) = y, date.month(t) = m, date.day(t) = d
       For invalid triples the selectors are unconstrained apart from the
       validity axioms, i.e. t denotes an unspecified valid date.
    */
    void theory_date::add_mk_axioms(app* t) {
        expr* y = t->get_arg(0);
        expr* mo = t->get_arg(1);
        expr* d = t->get_arg(2);
        expr_ref valid(u.mk_valid_expr(y, mo, d), m);
        m_rw(valid);
        if (m.is_false(valid))
            // invalid constructor application: the selectors are only
            // constrained by the validity axioms
            return;
        expr_ref ye(m.mk_eq(u.mk_year(t), y), m);
        expr_ref me(m.mk_eq(u.mk_month(t), mo), m);
        expr_ref de(m.mk_eq(u.mk_day(t), d), m);
        m_rw(ye);
        m_rw(me);
        m_rw(de);
        if (m.is_true(valid)) {
            assert_axiom(ye);
            assert_axiom(me);
            assert_axiom(de);
            return;
        }
        literal lv = mk_literal(valid);
        ctx.mark_as_relevant(lv);
        for (expr* e : { ye.get(), me.get(), de.get() }) {
            if (m.is_true(e))
                continue;
            literal l = mk_literal(e);
            ctx.mark_as_relevant(l);
            ctx.mk_th_axiom(get_id(), ~lv, l);
        }
    }

    /**
       For t = (date.add x py pm pd) assert
           rata_die(t) = add_rata_die(x, py, pm, pd)
       where rata_die is the day-number bijection between calendar-valid
       dates and integers, and add_rata_die performs month normalization
       and the end-of-month clamp followed by day addition. Together with
       the validity axioms for t this pins down exactly one date.
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
        enode* nx = ctx.get_enode(x);
        ensure_date_axioms(nx);
        enode* nt = ctx.get_enode(t);
        ensure_date_axioms(nt);
        theory_var vx = nx->get_th_var(get_id());
        theory_var vt = nt->get_th_var(get_id());
        expr_ref lhs(u.mk_rata_die_expr(year_of(vt), month_of(vt), day_of(vt)), m);
        expr_ref rhs(u.mk_add_rata_die_expr(year_of(vx), month_of(vx), day_of(vx), py, pm, pd), m);
        assert_axiom(m.mk_eq(lhs, rhs));
    }

    /**
       Comparison atoms are mapped to integer comparisons of day numbers.
       On calendar-valid dates the day-number order coincides with the
       lexicographic order on (year, month, day).
    */
    void theory_date::add_cmp_axioms(literal lit, app* atom) {
        enode* n1 = ctx.get_enode(atom->get_arg(0));
        enode* n2 = ctx.get_enode(atom->get_arg(1));
        ensure_date_axioms(n1);
        ensure_date_axioms(n2);
        theory_var v1 = n1->get_th_var(get_id());
        theory_var v2 = n2->get_th_var(get_id());
        expr_ref r1(u.mk_rata_die_expr(year_of(v1), month_of(v1), day_of(v1)), m);
        expr_ref r2(u.mk_rata_die_expr(year_of(v2), month_of(v2), day_of(v2)), m);
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
        literal l = mk_literal(cmp);
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), ~lit, l);
        ctx.mk_th_axiom(get_id(), lit, ~l);
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
