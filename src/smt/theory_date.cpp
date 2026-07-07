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

    static int s_theory_date_count = 0;
    theory_date::theory_date(context& ctx) :
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        u(ctx.get_manager()),
        m_rw(ctx.get_manager()),
        m_trail(ctx.get_manager()) {
        // the arithmetic solver expects atoms with numerals isolated on one side
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_rw.updt_params(p);
        fprintf(stderr, "DBG theory_date ctor #%d\n", ++s_theory_date_count);
    }

    theory_date::~theory_date() {
        for (auto const& [t, ra] : m_reps)
            dealloc(ra);
        m_reps.reset();
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
    void theory_date::ensure_epoch(enode* n) {
        SASSERT(u.is_date(n->get_expr()));
        theory_var v = mk_var(n);
        if (m_var2rep[v].m_epoch)
            return;
        app* t = to_app(n->get_expr());
        app_ref ep(u.mk_epoch(t), m);
        ctx.internalize(ep, false);
        m_var2rep[v].m_epoch = ctx.get_enode(ep);

        if (u.is_add(t) || u.is_sub(t)) {
            // the epoch definition refers to the epoch (or the components)
            // of the first argument
            arith_util& a = u.arith();
            rational rpy, rpm;
            if (a.is_numeral(t->get_arg(1), rpy) && rpy.is_zero() &&
                a.is_numeral(t->get_arg(2), rpm) && rpm.is_zero())
                ensure_epoch(ctx.get_enode(t->get_arg(0)));
            else
                ensure_civil(ctx.get_enode(t->get_arg(0)));
        }

        rep_axioms& ra = get_rep_axioms(t);
        if (ra.m_epoch_def)
            assert_axiom_eq(ep, ra.m_epoch_def);
        if (ra.m_epoch_def2)
            assert_axiom_eq(ep, ra.m_epoch_def2);
        assert_axioms(ra.m_epoch_fmls);
        if (ra.m_year) {
            // terms whose civil layer is part of their definition
            set_civil(v, ra);
            if (ra.m_civil_def)
                assert_axiom_eq(ep, ra.m_civil_def);
            assert_axioms(ra.m_civil_fmls);
        }
    }

    // Record the civil components on the variable, with a trail entry that
    // clears them on backtracking: the axioms asserted alongside are undone
    // by the backtracking as well, so a cleared field faithfully means "the
    // civil layer is not asserted in the current scope".
    void theory_date::set_civil(theory_var v, rep_axioms const& ra) {
        struct reset_civil : public trail {
            theory_date& th;
            theory_var v;
            reset_civil(theory_date& th, theory_var v): th(th), v(v) {}
            void undo() override {
                if ((unsigned)v < th.m_var2rep.size()) {
                    var_rep& r = th.m_var2rep[v];
                    r.m_year = nullptr;
                    r.m_month = nullptr;
                    r.m_day = nullptr;
                }
            }
        };
        var_rep& rep = m_var2rep[v];
        if (!rep.m_year)
            ctx.push_trail(reset_civil(*this, v));
        rep.m_year = ra.m_year;
        rep.m_month = ra.m_month;
        rep.m_day = ra.m_day;
    }

    void theory_date::ensure_civil(enode* n) {
        ensure_epoch(n);
        theory_var v = n->get_th_var(get_id());
        if (m_var2rep[v].m_year)
            return;
        app* t = to_app(n->get_expr());
        rep_axioms& ra = get_rep_axioms(t);
        if (!ra.m_year)
            build_civil(t, ra);
        set_civil(v, ra);
        app_ref ep(u.mk_epoch(t), m);
        if (ra.m_civil_def)
            assert_axiom_eq(ep, ra.m_civil_def);
        assert_axioms(ra.m_civil_fmls);
    }

    /**
       Build (or retrieve) the epoch-layer axioms of date term t. The
       result is cached for the lifetime of the solver, so
       re-internalization reuses the same fresh constants and atoms.
    */
    theory_date::rep_axioms& theory_date::get_rep_axioms(app* t) {
        rep_axioms* rap = nullptr;
        if (m_reps.find(t, rap))
            return *rap;
        rap = alloc(rep_axioms, m);
        m_reps.insert(t, rap);
        m_trail.push_back(t);
        rep_axioms& ra = *rap;
        arith_util& a = u.arith();

        rational vy, vm, vd;
        if (u.is_numeral_mk(t, vy, vm, vd) && date_decl_plugin::is_valid_civil(vy, vm, vd)) {
            // ground fast path: the epoch and the components are numerals
            ra.m_year = t->get_arg(0);
            ra.m_month = t->get_arg(1);
            ra.m_day = t->get_arg(2);
            ra.m_epoch_def = a.mk_numeral(date_decl_plugin::civil_to_days(vy, vm, vd), true);
            return ra;
        }

        if (u.is_mk(t)) {
            // strict constructor semantics: the components are exactly the
            // arguments; the validity bounds of the civil representation
            // make the occurrence infeasible for invalid argument triples
            build_civil(t, ra);
            ra.m_civil_fmls.push_back(m.mk_eq(ra.m_year, t->get_arg(0)));
            ra.m_civil_fmls.push_back(m.mk_eq(ra.m_month, t->get_arg(1)));
            ra.m_civil_fmls.push_back(m.mk_eq(ra.m_day, t->get_arg(2)));
            return ra;
        }

        app_ref ep(u.mk_epoch(t), m);
        if (u.is_add(t) || u.is_sub(t)) {
            expr* arg = t->get_arg(0);
            rational rpy, rpm;
            if (a.is_numeral(t->get_arg(1), rpy) && rpy.is_zero() &&
                a.is_numeral(t->get_arg(2), rpm) && rpm.is_zero()) {
                // pure day offsets shift the epoch directly: with a zero month
                // offset the day clamp is the identity
                expr* pd = t->get_arg(3);
                expr_ref ep0(u.mk_epoch(arg), m);
                ra.m_epoch_def = u.is_sub(t) ? a.mk_sub(ep0, pd) : a.mk_add(ep0, pd);
            }
            else {
                // the caller (ensure_epoch) materializes the civil layer of
                // the argument before these axioms are asserted
                rep_axioms& arep = get_rep_axioms(to_app(arg));
                SASSERT(arep.m_year);
                ra.m_epoch_def = u.mk_epoch_add(arep.m_year, arep.m_month, arep.m_day,
                                                t->get_arg(1), t->get_arg(2), t->get_arg(3),
                                                u.is_sub(t), ra.m_epoch_fmls);
            }
        }
        // the epoch determines the date; the range bounds make the term
        // denote a valid in-range date
        ra.m_epoch_fmls.push_back(a.mk_le(a.mk_numeral(date_decl_plugin::min_epoch(), true), ep));
        ra.m_epoch_fmls.push_back(a.mk_le(ep, a.mk_numeral(date_decl_plugin::max_epoch(), true)));
        return ra;
    }

    /**
       Materialize the civil layer of t: fresh (year, month, day) constants
       constrained to range over valid in-range dates, together with the
       epoch computation over them.
    */
    void theory_date::build_civil(app* t, rep_axioms& ra) {
        SASSERT(!ra.m_year);
        expr_ref y(m), mo(m), d(m);
        u.mk_civil_consts(y, mo, d);
        ra.m_year = y;
        ra.m_month = mo;
        ra.m_day = d;
        ra.m_civil_def = u.mk_civil_rep(y, mo, d, ra.m_civil_fmls);
    }

    bool theory_date::internalize_term(app* term) {
        fprintf(stderr, "DBG internalize_term\n");
        for (expr* arg : *term)
            ctx.internalize(arg, false);

        enode* e = ctx.e_internalized(term) ? ctx.get_enode(term) : ctx.mk_enode(term, false, false, true);
        mk_var(e);

        if (u.is_year(term) || u.is_month(term) || u.is_day(term)) {
            enode* arg = ctx.get_enode(term->get_arg(0));
            ensure_civil(arg);
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
        ensure_epoch(ctx.get_enode(x));
        ensure_epoch(ctx.get_enode(y));
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
        if (x != y)
            link_eq(x, y);
    }

    /**
       Couple the equality of two date terms with their epoch and civil
       component equalities, and add the epoch trichotomy:
       - x = y implies equal epochs and pairwise equal components (so
         equated dates collapse to one civil representation instead of an
         arithmetic inversion of the epoch computation),
       - equal components or equal epochs imply x = y (injectivity),
       - epochs are equal or strictly ordered one way or the other, which
         keeps ordering decisions at the level of bound propagation.
       Invoked for date pairs that interact: compared, equated or
       distinguished pairs.
    */
    void theory_date::link_eq(expr* x, expr* y) {
        enode* nx = ctx.get_enode(x);
        enode* ny = ctx.get_enode(y);
        ensure_epoch(nx);
        ensure_epoch(ny);
        var_rep const& rx = m_var2rep[nx->get_th_var(get_id())];
        var_rep const& ry = m_var2rep[ny->get_th_var(get_id())];
        arith_util& a = u.arith();
        literal eqd = mk_eq(x, y, false);
        ctx.mark_as_relevant(eqd);
        auto imp = [&](expr* s, expr* t) {
            if (s == t)
                return;
            literal l = mk_eq(s, t, false);
            ctx.mark_as_relevant(l);
            ctx.mk_th_axiom(get_id(), ~eqd, l);
        };
        expr* epx = rx.m_epoch->get_expr();
        expr* epy = ry.m_epoch->get_expr();
        imp(epx, epy);
        if (rx.m_year && ry.m_year) {
            imp(rx.m_year, ry.m_year);
            imp(rx.m_month, ry.m_month);
            imp(rx.m_day, ry.m_day);
            // equal components => equal dates (injectivity of the constructor)
            rational r1, r2;
            bool trivial = false;
            literal_vector lits;
            auto diff = [&](expr* s, expr* t) {
                if (s == t)
                    return;
                if (a.is_numeral(s, r1) && a.is_numeral(t, r2) && r1 != r2)
                    trivial = true;
                else {
                    literal l = mk_eq(s, t, false);
                    ctx.mark_as_relevant(l);
                    lits.push_back(~l);
                }
            };
            diff(rx.m_year, ry.m_year);
            diff(rx.m_month, ry.m_month);
            diff(rx.m_day, ry.m_day);
            if (!trivial) {
                lits.push_back(eqd);
                ctx.mk_th_axiom(get_id(), lits.size(), lits.data());
            }
        }
        // equal epochs => equal dates, and epoch trichotomy
        if (epx != epy) {
            literal eqe = mk_eq(epx, epy, false);
            ctx.mark_as_relevant(eqe);
            ctx.mk_th_axiom(get_id(), eqd, ~eqe);
            expr_ref lt1(a.mk_lt(epx, epy), m), lt2(a.mk_lt(epy, epx), m);
            m_rw(lt1);
            m_rw(lt2);
            literal l1 = mk_literal(lt1);
            literal l2 = mk_literal(lt2);
            ctx.mark_as_relevant(l1);
            ctx.mark_as_relevant(l2);
            ctx.mk_th_axiom(get_id(), eqe, l1, l2);
        }
    }

    bool theory_date::internalize_atom(app* atom, bool gate_ctx) {
        fprintf(stderr, "DBG internalize_atom\n");
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
            ensure_epoch(n);
    }

    // The epoch map is injective: equal epochs imply equal dates.
    // Merged dates propagate their epoch and component equalities.
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
        if (u.is_date(x) && u.is_date(y) && x != y)
            link_eq(x, y);
    }

    // Distinct dates have distinct epochs (and the full pair coupling).
    void theory_date::new_diseq_eh(theory_var v1, theory_var v2) {
        expr* x = get_enode(v1)->get_expr();
        expr* y = get_enode(v2)->get_expr();
        if (!u.is_date(x) || !u.is_date(y) || x == y)
            return;
        link_eq(x, y);
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
