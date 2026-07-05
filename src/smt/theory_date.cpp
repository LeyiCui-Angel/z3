/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Theory solver for calendar dates (legacy SMT core).
    See theory_date.h for an overview.

Author:

    Angel Cui's date theory task 2026-07-04

--*/
#include "smt/theory_date.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "ast/ast_pp.h"

namespace smt {

    theory_date::theory_date(context& ctx) :
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        u(ctx.get_manager()),
        m_rw(ctx.get_manager()),
        m_trail(ctx.get_manager()) {
        // the arithmetic solver expects atoms with numerals isolated on one side
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
        m_var2rep.reserve(v + 1);
        return v;
    }

    void theory_date::pop_scope_eh(unsigned num_scopes) {
        theory::pop_scope_eh(num_scopes);
        m_var2rep.shrink(get_num_vars());
    }

    void theory_date::assert_axiom(expr* e) {
        expr_ref f(e, m);
        m_rw(f);
        if (m.is_true(f))
            return;
        literal l = mk_literal(f);
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), 1, &l);
    }

    void theory_date::assert_axioms(expr_ref_vector const& fmls) {
        for (expr* e : fmls)
            assert_axiom(e);
    }

    // Assert lhs = rhs, simplifying only rhs. The left-hand side is a
    // date.epoch application that must stay in the asserted atom: the
    // rewriter would fold epochs of ground dates into numerals, leaving
    // the application itself unconstrained.
    void theory_date::assert_axiom_eq(expr* lhs, expr* rhs) {
        expr_ref r(rhs, m);
        m_rw(r);
        if (lhs == r)
            return;
        literal l = mk_eq(lhs, r, false);
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), 1, &l);
    }

    /**
       Associate an epoch term and civil component terms with the date term
       of enode n, and assert the axioms defining them. For date.mk,
       date.add and date.sub terms the epoch is additionally constrained by
       the arguments of the term.
    */
    void theory_date::ensure_rep(enode* n) {
        SASSERT(u.is_date(n->get_expr()));
        theory_var v = mk_var(n);
        if (m_var2rep[v].m_epoch)
            return;
        app* t = to_app(n->get_expr());
        app_ref ep(u.mk_epoch(t), m);
        ctx.internalize(ep, false);
        var_rep& rep = m_var2rep[v];
        rep.m_epoch = ctx.get_enode(ep);
        arith_util& a = u.arith();

        rational vy, vm, vd;
        if (u.is_numeral_mk(t, vy, vm, vd)) {
            // ground fast path: the epoch and the components are numerals
            rational en = date_decl_plugin::civil_to_days(vy, vm, vd);
            date_decl_plugin::days_to_civil(en, vy, vm, vd);
            rep.m_year = a.mk_numeral(vy, true);
            rep.m_month = a.mk_numeral(vm, true);
            rep.m_day = a.mk_numeral(vd, true);
            m_trail.push_back(rep.m_year);
            m_trail.push_back(rep.m_month);
            m_trail.push_back(rep.m_day);
            assert_axiom_eq(ep, a.mk_numeral(en, true));
            return;
        }

        // civil decomposition: y/mo/d are functionally determined by the epoch
        expr_ref_vector fmls(m);
        expr_ref y(m), mo(m), d(m);
        expr_ref civil_epoch = u.mk_civil_rep(y, mo, d, fmls);
        rep.m_year = y;
        rep.m_month = mo;
        rep.m_day = d;
        m_trail.push_back(y);
        m_trail.push_back(mo);
        m_trail.push_back(d);
        assert_axiom_eq(ep, civil_epoch);

        if (u.is_mk(t))
            assert_axiom_eq(ep, u.mk_epoch_of_ymd(t->get_arg(0), t->get_arg(1), t->get_arg(2), fmls));
        else if (u.is_add(t) || u.is_sub(t)) {
            enode* arg = ctx.get_enode(t->get_arg(0));
            ensure_rep(arg);
            expr_ref ep0(u.mk_epoch(t->get_arg(0)), m);
            rational rpy, rpm;
            if (a.is_numeral(t->get_arg(1), rpy) && rpy.is_zero() &&
                a.is_numeral(t->get_arg(2), rpm) && rpm.is_zero()) {
                // pure day offsets shift the epoch directly: with a zero month
                // offset the day clamp is the identity
                expr* pd = t->get_arg(3);
                assert_axiom_eq(ep, u.is_sub(t) ? a.mk_sub(ep0, pd) : a.mk_add(ep0, pd));
            }
            else {
                var_rep const& arep = m_var2rep[arg->get_th_var(get_id())];
                assert_axiom_eq(ep, u.mk_epoch_add(arep.m_year, arep.m_month, arep.m_day,
                                                   t->get_arg(1), t->get_arg(2), t->get_arg(3),
                                                   u.is_sub(t), fmls));
            }
        }
        assert_axioms(fmls);
    }

    bool theory_date::internalize_term(app* term) {
        for (expr* arg : *term)
            ctx.internalize(arg, false);

        enode* e = ctx.e_internalized(term) ? ctx.get_enode(term) : ctx.mk_enode(term, false, false, true);
        mk_var(e);

        if (u.is_year(term) || u.is_month(term) || u.is_day(term)) {
            enode* arg = ctx.get_enode(term->get_arg(0));
            ensure_rep(arg);
            var_rep const& rep = m_var2rep[arg->get_th_var(get_id())];
            if (u.is_year(term))
                assert_axiom(m.mk_eq(term, rep.m_year));
            else if (u.is_month(term))
                assert_axiom(m.mk_eq(term, rep.m_month));
            else
                assert_axiom(m.mk_eq(term, rep.m_day));
        }
        // date.mk/date.add/date.sub get their axioms via apply_sort_cnstr,
        // which the context invokes for every date-sorted enode.
        // date.epoch terms carry no axioms of their own.
        return true;
    }

    void theory_date::internalize_cmp(app* atom) {
        expr* x = atom->get_arg(0);
        expr* y = atom->get_arg(1);
        ensure_rep(ctx.get_enode(x));
        ensure_rep(ctx.get_enode(y));
        arith_util& a = u.arith();
        expr_ref epx(u.mk_epoch(x), m), epy(u.mk_epoch(y), m);
        expr_ref cmp(m);
        if (u.is_lt(atom))
            cmp = a.mk_lt(epx, epy);
        else if (u.is_le(atom))
            cmp = a.mk_le(epx, epy);
        else if (u.is_gt(atom))
            cmp = a.mk_gt(epx, epy);
        else
            cmp = a.mk_ge(epx, epy);
        m_rw(cmp);
        literal lit(ctx.get_bool_var(atom), false);
        literal cl = mk_literal(cmp);
        ctx.mark_as_relevant(cl);
        ctx.mk_th_axiom(get_id(), ~lit, cl);
        ctx.mk_th_axiom(get_id(), lit, ~cl);
    }

    bool theory_date::internalize_atom(app* atom, bool gate_ctx) {
        SASSERT(u.is_lt(atom) || u.is_le(atom) || u.is_gt(atom) || u.is_ge(atom));
        for (expr* arg : *atom)
            ctx.internalize(arg, false);
        bool_var bv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(bv, get_id());
        ctx.mark_as_relevant(bv);
        internalize_cmp(atom);
        return true;
    }

    void theory_date::apply_sort_cnstr(enode* n, sort* s) {
        if (u.is_date(s))
            ensure_rep(n);
    }

    // The epoch map is injective: equal epochs imply equal dates.
    void theory_date::new_eq_eh(theory_var v1, theory_var v2) {
        expr* x = get_enode(v1)->get_expr();
        expr* y = get_enode(v2)->get_expr();
        expr* dx = nullptr, * dy = nullptr;
        if (u.is_epoch(x, dx) && u.is_epoch(y, dy) && dx != dy) {
            literal eq_ep = mk_eq(x, y, false);
            literal eq_d = mk_eq(dx, dy, false);
            ctx.mark_as_relevant(eq_ep);
            ctx.mark_as_relevant(eq_d);
            ctx.mk_th_axiom(get_id(), ~eq_ep, eq_d);
        }
    }

    // Distinct dates have distinct epochs.
    void theory_date::new_diseq_eh(theory_var v1, theory_var v2) {
        expr* x = get_enode(v1)->get_expr();
        expr* y = get_enode(v2)->get_expr();
        if (!u.is_date(x) || !u.is_date(y))
            return;
        expr_ref epx(u.mk_epoch(x), m), epy(u.mk_epoch(y), m);
        literal eq_d = mk_eq(x, y, false);
        literal eq_ep = mk_eq(epx, epy, false);
        ctx.mark_as_relevant(eq_d);
        ctx.mark_as_relevant(eq_ep);
        ctx.mk_th_axiom(get_id(), eq_d, ~eq_ep);
    }

    // --- model generation ------------------------------------------------

    class theory_date::date_value_proc : public model_value_proc {
        theory_date& th;
        enode*       m_epoch;
    public:
        date_value_proc(theory_date& th, enode* ep) : th(th), m_epoch(ep) {}
        void get_dependencies(buffer<model_value_dependency>& result) override {
            result.push_back(model_value_dependency(m_epoch));
        }
        app* mk_value(model_generator& mg, expr_ref_vector const& values) override {
            rational n(0);
            if (!values.empty())
                th.u.arith().is_numeral(values[0], n);
            app* val = th.u.mk_value_from_epoch(n);
            th.m_factory->register_value(n);
            th.m_factory->add_trail(val);
            return val;
        }
    };

    void theory_date::init_model(model_generator& mg) {
        m_factory = alloc(date_factory, m, get_family_id());
        mg.register_factory(m_factory);
    }

    model_value_proc* theory_date::mk_value(enode* n, model_generator& mg) {
        enode* ep = nullptr;
        for (enode* sib : *n) {
            theory_var v = sib->get_th_var(get_id());
            if (v != null_theory_var && (unsigned)v < m_var2rep.size() && m_var2rep[v].m_epoch) {
                ep = m_var2rep[v].m_epoch;
                break;
            }
        }
        if (!ep)
            return alloc(expr_wrapper_proc, to_app(m_factory->get_fresh_value(n->get_sort())));
        return alloc(date_value_proc, *this, ep);
    }

}
