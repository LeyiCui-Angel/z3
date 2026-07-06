/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Theory solver for calendar dates.

Author:

    Angel Cui 2026-03-23

--*/

#include "ast/ast_pp.h"
#include "model/value_factory.h"
#include "smt/theory_date.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"

namespace smt {

    // produces fresh calendar-valid dates by walking the Rata Die numbering
    class date_factory : public value_factory {
        date_util           u;
        arith_util          a;
        rational            m_next;
        obj_hashtable<expr> m_used;
        expr_ref_vector     m_trail;

        app* mk_date(rational const& n) {
            rational y, d;
            unsigned mo;
            date_util::rata_die_inv(n, y, mo, d);
            return u.mk_mk(a.mk_numeral(y, true), a.mk_numeral(rational(mo), true), a.mk_numeral(d, true));
        }

    public:
        date_factory(ast_manager& m, family_id fid):
            value_factory(m, fid),
            u(m),
            a(m),
            m_next(1),
            m_trail(m) {}

        expr* get_some_value(sort* s) override {
            return mk_date(rational(1));
        }

        bool get_some_values(sort* s, expr_ref& v1, expr_ref& v2) override {
            v1 = mk_date(rational(1));
            v2 = mk_date(rational(2));
            return true;
        }

        expr* get_fresh_value(sort* s) override {
            app* r = mk_date(m_next);
            m_next += rational(1);
            while (m_used.contains(r)) {
                r = mk_date(m_next);
                m_next += rational(1);
            }
            register_value(r);
            return r;
        }

        void register_value(expr* n) override {
            if (!m_used.contains(n)) {
                m_used.insert(n);
                m_trail.push_back(n);
            }
        }
    };

    class date_value_proc : public model_value_proc {
        ast_manager& m;
        enode*       m_deps[3]; // year, month, day

    public:
        date_value_proc(ast_manager& m, enode* y, enode* mo, enode* d): m(m) {
            m_deps[0] = y;
            m_deps[1] = mo;
            m_deps[2] = d;
        }

        void get_dependencies(buffer<model_value_dependency>& result) override {
            for (enode* n : m_deps)
                result.push_back(model_value_dependency(n));
        }

        app* mk_value(model_generator& mg, expr_ref_vector const& values) override {
            date_util u(m);
            arith_util a(m);
            rational y, mo, d;
            if (a.is_numeral(values[0], y) && a.is_numeral(values[1], mo) && a.is_numeral(values[2], d))
                return u.mk_mk(a.mk_numeral(y, true), a.mk_numeral(mo, true), a.mk_numeral(d, true));
            return u.mk_mk(a.mk_int(1), a.mk_int(1), a.mk_int(1));
        }
    };

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        u(m),
        a(m),
        m_rw(m),
        m_values_trail(m) {
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_rw.updt_params(p);
    }

    theory_var theory_date::mk_var(enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        theory_var v = theory::mk_var(n);
        ctx.attach_th_var(n, this, v);
        ctx.mark_as_relevant(n);
        return v;
    }

    void theory_date::assert_axiom(expr* e) {
        expr_ref f(e, m);
        m_rw(f);
        if (m.is_true(f))
            return;
        TRACE(date, tout << "assert: " << mk_pp(f, m) << "\n";);
        if (m.has_trace_stream())
            log_axiom_instantiation(f);
        ctx.internalize(f, false);
        if (m.has_trace_stream())
            m.trace_stream() << "[end-of-instance]\n";
        literal lit(ctx.get_literal(f));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }

    // assert e verbatim, without running the rewriter: used for selector
    // equations of concrete constructor applications, where the rewriter
    // would fold the selector term away and leave no enode for congruence
    void theory_date::assert_axiom_norewrite(expr* e) {
        expr_ref f(e, m);
        TRACE(date, tout << "assert (no rewrite): " << mk_pp(f, m) << "\n";);
        if (m.has_trace_stream())
            log_axiom_instantiation(f);
        ctx.internalize(f, false);
        if (m.has_trace_stream())
            m.trace_stream() << "[end-of-instance]\n";
        literal lit(ctx.get_literal(f));
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }

    void theory_date::assert_implies(expr* premise, expr* conseq) {
        expr_ref p(premise, m), c(conseq, m);
        m_rw(p);
        m_rw(c);
        if (m.is_false(p) || m.is_true(c))
            return;
        if (m.is_true(p)) {
            assert_axiom(c);
            return;
        }
        ctx.internalize(p, false);
        ctx.internalize(c, false);
        literal lp(ctx.get_literal(p));
        literal lc(ctx.get_literal(c));
        ctx.mark_as_relevant(lp);
        ctx.mark_as_relevant(lc);
        ctx.mk_th_axiom(get_id(), ~lp, lc);
    }

    void theory_date::assert_iff(literal lit, expr* def) {
        expr_ref d(def, m);
        m_rw(d);
        if (m.is_true(d)) {
            ctx.mk_th_axiom(get_id(), 1, &lit);
            return;
        }
        if (m.is_false(d)) {
            literal nlit = ~lit;
            ctx.mk_th_axiom(get_id(), 1, &nlit);
            return;
        }
        ctx.internalize(d, false);
        literal ld(ctx.get_literal(d));
        ctx.mark_as_relevant(ld);
        ctx.mk_th_axiom(get_id(), ~lit, ld);
        ctx.mk_th_axiom(get_id(), lit, ~ld);
    }

    expr* theory_date::mk_neg(expr* e) {
        rational r;
        if (a.is_numeral(e, r))
            return a.mk_numeral(-r, true);
        return a.mk_uminus(e);
    }

    expr_ref theory_date::mk_rata_die(expr* d) {
        return u.mk_rata_die(u.mk_year(d), u.mk_month(d), u.mk_day(d));
    }

    // phase preference, not an axiom: try to place years in the familiar
    // calendar range first, so that unconstrained dates receive natural
    // model values; out-of-range years remain reachable when required
    void theory_date::add_year_range_preference(expr* y) {
        expr_ref lo(a.mk_ge(y, a.mk_int(1)), m), hi(a.mk_le(y, a.mk_int(9999)), m);
        for (expr* b : { lo.get(), hi.get() }) {
            ctx.internalize(b, false);
            literal l = ctx.get_literal(b);
            if (l.sign())
                continue;
            ctx.mark_as_relevant(l);
            ctx.set_true_first_flag(l.var());
        }
    }

    // every Date term denotes a calendar-valid date and is reconstructed
    // from its selector triple
    void theory_date::add_date_axioms(enode* n) {
        expr* t = n->get_expr();
        SASSERT(u.is_date(t));
        expr_ref y(u.mk_year(t), m), mo(u.mk_month(t), m), d(u.mk_day(t), m);
        add_year_range_preference(y);
        assert_axiom(a.mk_le(a.mk_int(1), mo));
        assert_axiom(a.mk_le(mo, a.mk_int(12)));
        assert_axiom(a.mk_le(a.mk_int(1), d));
        assert_axiom(a.mk_le(d, u.mk_days_in_month(y, mo)));
        // t = (date.mk (date.year t) (date.month t) (date.day t));
        // skipped when t already has this shape to ensure termination
        if (u.is_selector_mk(t))
            return;
        assert_axiom(m.mk_eq(t, u.mk_mk(y, mo, d)));
    }

    // selector axioms for valid constructor applications
    void theory_date::add_mk_axioms(app* term) {
        expr* y = term->get_arg(0);
        expr* mo = term->get_arg(1);
        expr* d = term->get_arg(2);
        rational ry, rm, rd;
        if (a.is_numeral(y, ry) && a.is_numeral(mo, rm) && a.is_numeral(d, rd)) {
            if (date_util::is_valid_date(ry, rm, rd)) {
                // assert the selector equations verbatim: the rewriter would
                // evaluate the selectors to the numerals, dropping the enodes
                // needed to propagate the components to congruent date terms
                assert_axiom_norewrite(m.mk_eq(u.mk_year(term), y));
                assert_axiom_norewrite(m.mk_eq(u.mk_month(term), mo));
                assert_axiom_norewrite(m.mk_eq(u.mk_day(term), d));
            }
            // invalid concrete constructor applications are unspecified
            return;
        }
        // symbolic date construction carries an implicit validity obligation
        // on the argument triple; with it the selector equations hold
        // unconditionally
        assert_axiom(u.mk_is_valid(y, mo, d));
        assert_axiom(m.mk_eq(u.mk_year(term), y));
        assert_axiom(m.mk_eq(u.mk_month(term), mo));
        assert_axiom(m.mk_eq(u.mk_day(term), d));
    }

    // the Rata Die number of the result of date.add/date.sub relates the
    // result triple to the argument triple and the period
    void theory_date::add_arith_axioms(app* term, bool is_sub) {
        expr* d = term->get_arg(0);
        expr* py = term->get_arg(1);
        expr* pm = term->get_arg(2);
        expr* pd = term->get_arg(3);
        if (is_sub) {
            py = mk_neg(py);
            pm = mk_neg(pm);
            pd = mk_neg(pd);
        }
        rational rpy, rpm, rpd;
        if (a.is_numeral(py, rpy) && a.is_numeral(pm, rpm) && a.is_numeral(pd, rpd) &&
            rpy.is_int() && rpm.is_int() && rpd.is_int() &&
            abs(rpd) <= date_util::mk_add_triple_bound()) {
            // concrete period: the result triple is a bounded case split
            // over the argument month and the day carry
            expr_ref ry(m), rmo(m), rdy(m);
            u.mk_add_triple(u.mk_year(d), u.mk_month(d), u.mk_day(d), rpy, rpm, rpd, ry, rmo, rdy);
            assert_axiom(m.mk_eq(u.mk_year(term), ry));
            assert_axiom(m.mk_eq(u.mk_month(term), rmo));
            assert_axiom(m.mk_eq(u.mk_day(term), rdy));
            return;
        }
        expr_ref lhs = mk_rata_die(term);
        expr_ref rhs = u.mk_add_rata_die(u.mk_year(d), u.mk_month(d), u.mk_day(d), py, pm, pd);
        assert_axiom(m.mk_eq(lhs, rhs));
    }

    expr_ref theory_date::mk_lex_cmp(expr* x, expr* y, bool strict) {
        expr_ref yx(u.mk_year(x), m), yy(u.mk_year(y), m);
        expr_ref mx(u.mk_month(x), m), my(u.mk_month(y), m);
        expr_ref dx(u.mk_day(x), m), dy(u.mk_day(y), m);
        expr* day_cmp = strict ? a.mk_lt(dx, dy) : a.mk_le(dx, dy);
        return expr_ref(
            m.mk_or(a.mk_lt(yx, yy),
                    m.mk_and(m.mk_eq(yx, yy),
                             m.mk_or(a.mk_lt(mx, my),
                                     m.mk_and(m.mk_eq(mx, my), day_cmp)))), m);
    }

    // the Rata Die numbering is injective on calendar-valid dates:
    // distinct dates have distinct day numbers
    void theory_date::new_diseq_eh(theory_var v1, theory_var v2) {
        expr* x = get_enode(v1)->get_expr();
        expr* y = get_enode(v2)->get_expr();
        if (!u.is_date(x) || !u.is_date(y))
            return;
        expr_ref rd_eq(m.mk_eq(mk_rata_die(x), mk_rata_die(y)), m);
        m_rw(rd_eq);
        literal eq = mk_eq(x, y, false);
        ctx.internalize(rd_eq, false);
        literal l_rd(ctx.get_literal(rd_eq));
        ctx.mark_as_relevant(eq);
        ctx.mark_as_relevant(l_rd);
        ctx.mk_th_axiom(get_id(), eq, ~l_rd);
    }

    bool theory_date::internalize_atom(app* atom, bool gate_ctx) {
        for (expr* arg : *atom)
            ensure_enode(arg);
        bool_var bv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(bv, get_id());
        ctx.mark_as_relevant(bv);
        literal lit(bv, false);
        expr* x = atom->get_arg(0);
        expr* y = atom->get_arg(1);
        if (u.is_gt(atom) || u.is_ge(atom))
            std::swap(x, y);
        bool strict = u.is_lt(atom) || u.is_gt(atom);
        // lexicographic order on the selector triples ...
        assert_iff(lit, mk_lex_cmp(x, y, strict));
        // ... coincides with the order of Rata Die numbers on valid dates
        expr_ref rdx = mk_rata_die(x), rdy = mk_rata_die(y);
        assert_iff(lit, strict ? a.mk_lt(rdx, rdy) : a.mk_le(rdx, rdy));
        return true;
    }

    bool theory_date::internalize_term(app* term) {
        for (expr* arg : *term)
            ensure_enode(arg);
        enode* e = ctx.e_internalized(term) ? ctx.get_enode(term) : ctx.mk_enode(term, false, false, true);
        if (is_attached_to_var(e))
            return true;
        mk_var(e);
        // reconstruction terms (date.mk (date.year s) ...) need no axioms of
        // their own: the identity s = t asserted for s makes all their
        // properties available through congruence, and a second copy of the
        // validity constraints only burdens the arithmetic solver
        if (u.is_selector_mk(term))
            return true;
        if (u.is_date(term))
            add_date_axioms(e);
        if (u.is_mk(term))
            add_mk_axioms(term);
        else if (u.is_add(term))
            add_arith_axioms(term, false);
        else if (u.is_sub(term))
            add_arith_axioms(term, true);
        return true;
    }

    void theory_date::apply_sort_cnstr(enode* n, sort* s) {
        SASSERT(u.is_date(s));
        if (is_attached_to_var(n))
            return;
        mk_var(n);
        add_date_axioms(n);
    }

    void theory_date::init_model(model_generator& mg) {
        mg.register_factory(alloc(date_factory, m, get_family_id()));
    }

    model_value_proc* theory_date::mk_value(enode* n, model_generator& mg) {
        // use the selector terms of any class member that has them internalized
        for (enode* sib : *n) {
            expr* t = sib->get_expr();
            if (!u.is_date(t))
                continue;
            expr_ref y(u.mk_year(t), m), mo(u.mk_month(t), m), d(u.mk_day(t), m);
            if (ctx.e_internalized(y) && ctx.e_internalized(mo) && ctx.e_internalized(d))
                return alloc(date_value_proc, m, ctx.get_enode(y), ctx.get_enode(mo), ctx.get_enode(d));
        }
        arith_util a2(m);
        app* val = u.mk_mk(a2.mk_int(1), a2.mk_int(1), a2.mk_int(1));
        m_values_trail.push_back(val);
        return alloc(expr_wrapper_proc, val);
    }

    void theory_date::display(std::ostream& out) const {
        out << "theory date:\n";
        for (unsigned v = 0; v < get_num_vars(); ++v)
            out << v << " -> " << mk_pp(get_enode(v)->get_expr(), m) << "\n";
    }

}
