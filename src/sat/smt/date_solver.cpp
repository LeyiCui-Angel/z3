/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates (SAT/EUF core).
    See date_solver.h for an overview.

Author:

    Angel Cui's date theory task 2026-07-04

--*/
#include "ast/ast_pp.h"
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"

namespace dates {

    solver::solver(euf::solver& ctx) :
        th_euf_solver(ctx, symbol("date"), ctx.get_manager().mk_family_id("date")),
        u(ctx.get_manager()),
        m_rw(ctx.get_manager()),
        m_trail(ctx.get_manager()),
        m_next_fresh(0) {
        // the arithmetic solver expects atoms with numerals isolated on one side
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_rw.updt_params(p);
    }

    solver::~solver() {
        for (auto const& [t, ra] : m_reps)
            dealloc(ra);
        m_reps.reset();
    }

    euf::theory_var solver::mk_var(enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        theory_var v = th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, v);
        m_var2rep.reserve(v + 1);
        return v;
    }

    void solver::pop_core(unsigned num_scopes) {
        th_euf_solver::pop_core(num_scopes);
        m_var2rep.shrink(get_num_vars());
    }

    enode* solver::get_epoch(enode* n) const {
        theory_var v = n->get_th_var(get_id());
        if (v == euf::null_theory_var || (unsigned)v >= m_var2rep.size())
            return nullptr;
        return m_var2rep[v].m_epoch;
    }

    void solver::push_axiom(enode* n) {
        m_axiom_queue.push_back(n);
        ctx.push(push_back_vector<ptr_vector<enode>>(m_axiom_queue));
    }

    // Defer the coupling axioms of a date pair to unit_propagate: the
    // equality handlers run in the middle of congruence propagation and
    // backtracking, where fresh literals must not be created.
    void solver::push_link(expr* x, expr* y) {
        m_link_queue.push_back(std::make_pair(x, y));
        ctx.push(push_back_vector<svector<std::pair<expr*, expr*>>>(m_link_queue));
    }

    bool solver::unit_propagate() {
        force_push();
        if (m_qhead == m_axiom_queue.size() && m_lhead == m_link_queue.size())
            return false;
        ctx.push(value_trail<unsigned>(m_qhead));
        ctx.push(value_trail<unsigned>(m_lhead));
        for (; m_qhead < m_axiom_queue.size() && !s().inconsistent(); ++m_qhead)
            axiomatize(m_axiom_queue[m_qhead]);
        for (; m_lhead < m_link_queue.size() && !s().inconsistent(); ++m_lhead)
            link_eq(m_link_queue[m_lhead].first, m_link_queue[m_lhead].second);
        return true;
    }

    sat::check_result solver::check() {
        if (unit_propagate())
            return sat::check_result::CR_CONTINUE;
        return sat::check_result::CR_DONE;
    }

    void solver::add_axiom(expr* e) {
        expr_ref f(e, m);
        m_rw(f);
        if (m.is_true(f))
            return;
        add_unit(mk_literal(f));
    }

    void solver::add_axioms(expr_ref_vector const& fmls) {
        for (expr* e : fmls)
            add_axiom(e);
    }

    // Assert lhs = rhs, simplifying only rhs. The left-hand side is a
    // date.epoch application that must stay in the asserted atom: the
    // rewriter would fold epochs of ground dates into numerals, leaving
    // the application itself unconstrained.
    void solver::add_axiom_eq(expr* lhs, expr* rhs) {
        expr_ref r(rhs, m);
        m_rw(r);
        if (lhs == r)
            return;
        add_unit(eq_internalize(lhs, r));
    }

    /**
       Associate an epoch term and civil component terms with the date term
       of enode n, and assert the axioms defining them. For date.mk,
       date.add and date.sub terms the epoch is additionally constrained by
       the arguments of the term.
    */
    void solver::ensure_epoch(enode* n) {
        SASSERT(u.is_date(n->get_expr()));
        theory_var v = mk_var(n);
        app* t = to_app(n->get_expr());
        expr_ref ep(u.mk_epoch(t), m);
        // The cached epoch enode may be stale: backtracking over a user
        // scope destroys enodes without necessarily removing the theory
        // variable. Re-internalize and re-assert the axioms whenever the
        // current egraph does not hold the recorded enode (the axioms of
        // that scope were removed together with it).
        enode* epn = expr2enode(ep);
        if (epn && m_var2rep[v].m_epoch == epn)
            return;
        ctx.internalize(ep);
        m_var2rep[v].m_epoch = expr2enode(ep);

        if (u.is_add(t) || u.is_sub(t)) {
            // the epoch definition refers to the epoch (or the components)
            // of the first argument
            arith_util& a = u.arith();
            rational rpy, rpm;
            if (a.is_numeral(t->get_arg(1), rpy) && rpy.is_zero() &&
                a.is_numeral(t->get_arg(2), rpm) && rpm.is_zero())
                ensure_epoch(expr2enode(t->get_arg(0)));
            else
                ensure_civil(expr2enode(t->get_arg(0)));
        }

        rep_axioms& ra = get_rep_axioms(t);
        if (ra.m_epoch_def)
            add_axiom_eq(ep, ra.m_epoch_def);
        if (ra.m_epoch_def2)
            add_axiom_eq(ep, ra.m_epoch_def2);
        add_axioms(ra.m_epoch_fmls);
        if (ra.m_year && (m_var2rep[v].m_year || u.is_mk(t) || is_ground_valid_mk(t))) {
            // re-assert the civil layer whenever it was materialized for
            // this variable (or is part of the term's definition)
            set_civil(v, ra);
            if (ra.m_civil_def)
                add_axiom_eq(ep, ra.m_civil_def);
            add_axioms(ra.m_civil_fmls);
        }
    }

    bool solver::is_ground_valid_mk(app* t) const {
        rational vy, vm, vd;
        date_util& uu = const_cast<date_util&>(u);
        return uu.is_numeral_mk(t, vy, vm, vd) && date_decl_plugin::is_valid_civil(vy, vm, vd);
    }

    // Record the civil components on the variable, with a trail entry that
    // clears them on backtracking: the axioms asserted alongside are undone
    // by the backtracking as well, so a cleared field faithfully means "the
    // civil layer is not asserted in the current scope".
    void solver::set_civil(theory_var v, rep_axioms const& ra) {
        struct reset_civil : public trail {
            solver& s;
            theory_var v;
            reset_civil(solver& s, theory_var v): s(s), v(v) {}
            void undo() override {
                if ((unsigned)v < s.m_var2rep.size()) {
                    var_rep& r = s.m_var2rep[v];
                    r.m_year = nullptr;
                    r.m_month = nullptr;
                    r.m_day = nullptr;
                }
            }
        };
        var_rep& rep = m_var2rep[v];
        if (!rep.m_year)
            ctx.push(reset_civil(*this, v));
        rep.m_year = ra.m_year;
        rep.m_month = ra.m_month;
        rep.m_day = ra.m_day;
    }

    void solver::ensure_civil(enode* n) {
        ensure_epoch(n);
        theory_var v = n->get_th_var(get_id());
        if (m_var2rep[v].m_year)
            return;
        app* t = to_app(n->get_expr());
        rep_axioms& ra = get_rep_axioms(t);
        if (!ra.m_year)
            build_civil(t, ra);
        set_civil(v, ra);
        expr_ref ep(u.mk_epoch(t), m);
        if (ra.m_civil_def)
            add_axiom_eq(ep, ra.m_civil_def);
        add_axioms(ra.m_civil_fmls);
    }

    /**
       Build (or retrieve) the epoch-layer axioms of date term t. The
       result is cached for the lifetime of the solver, so
       re-axiomatization after backtracking reuses the same fresh
       constants and atoms.
    */
    solver::rep_axioms& solver::get_rep_axioms(app* t) {
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

        expr_ref ep(u.mk_epoch(t), m);
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
    void solver::build_civil(app* t, rep_axioms& ra) {
        SASSERT(!ra.m_year);
        expr_ref y(m), mo(m), d(m);
        u.mk_civil_consts(y, mo, d);
        ra.m_year = y;
        ra.m_month = mo;
        ra.m_day = d;
        ra.m_civil_def = u.mk_civil_rep(y, mo, d, ra.m_civil_fmls);
    }

    void solver::axiomatize(enode* n) {
        expr* e = n->get_expr();
        if (u.is_date(e)) {
            ensure_epoch(n);
            return;
        }
        app* t = to_app(e);
        if (u.is_year(e) || u.is_month(e) || u.is_day(e)) {
            enode* arg = expr2enode(t->get_arg(0));
            ensure_civil(arg);
            var_rep const& rep = m_var2rep[arg->get_th_var(get_id())];
            if (u.is_year(e))
                add_axiom(m.mk_eq(e, rep.m_year));
            else if (u.is_month(e))
                add_axiom(m.mk_eq(e, rep.m_month));
            else
                add_axiom(m.mk_eq(e, rep.m_day));
            return;
        }
        if (u.is_lt(e) || u.is_le(e) || u.is_gt(e) || u.is_ge(e)) {
            expr* x = t->get_arg(0);
            expr* yy = t->get_arg(1);
            ensure_epoch(expr2enode(x));
            ensure_epoch(expr2enode(yy));
            arith_util& a = u.arith();
            expr_ref epx(u.mk_epoch(x), m), epy(u.mk_epoch(yy), m);
            expr_ref cmp(m);
            if (u.is_lt(e))
                cmp = a.mk_lt(epx, epy);
            else if (u.is_le(e))
                cmp = a.mk_le(epx, epy);
            else if (u.is_gt(e))
                cmp = a.mk_gt(epx, epy);
            else
                cmp = a.mk_ge(epx, epy);
            m_rw(cmp);
            sat::literal lit = expr2literal(e);
            sat::literal cl = mk_literal(cmp);
            add_clause(~lit, cl);
            add_clause(lit, ~cl);
            if (x != yy)
                push_link(x, yy);
            return;
        }
        // date.epoch terms carry no axioms of their own
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
    void solver::link_eq(expr* x, expr* y) {
        enode* nx = expr2enode(x);
        enode* ny = expr2enode(y);
        ensure_epoch(nx);
        ensure_epoch(ny);
        var_rep const& rx = m_var2rep[nx->get_th_var(get_id())];
        var_rep const& ry = m_var2rep[ny->get_th_var(get_id())];
        arith_util& a = u.arith();
        sat::literal eqd = eq_internalize(x, y);
        auto imp = [&](expr* s, expr* t) {
            if (s != t)
                add_clause(~eqd, eq_internalize(s, t));
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
            sat::literal_vector lits;
            auto diff = [&](expr* s, expr* t) {
                if (s == t)
                    return;
                if (a.is_numeral(s, r1) && a.is_numeral(t, r2) && r1 != r2)
                    trivial = true;
                else
                    lits.push_back(~eq_internalize(s, t));
            };
            diff(rx.m_year, ry.m_year);
            diff(rx.m_month, ry.m_month);
            diff(rx.m_day, ry.m_day);
            if (!trivial) {
                lits.push_back(eqd);
                add_clause(lits);
            }
        }
        // equal epochs => equal dates, and epoch trichotomy
        if (epx != epy) {
            sat::literal eqe = eq_internalize(epx, epy);
            add_clause(eqd, ~eqe);
            expr_ref lt1(a.mk_lt(epx, epy), m), lt2(a.mk_lt(epy, epx), m);
            m_rw(lt1);
            m_rw(lt2);
            add_clause(eqe, mk_literal(lt1), mk_literal(lt2));
        }
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        sat::literal lit = expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e) {
        visit_rec(m, e, false, false);
    }

    bool solver::visited(expr* e) {
        enode* n = expr2enode(e);
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
        enode* n = expr2enode(e);
        if (!n)
            n = mk_enode(e, false);
        SASSERT(!n->is_attached_to(get_id()));
        mk_var(n);
        if (!u.is_epoch(e))
            push_axiom(n);
        return true;
    }

    void solver::apply_sort_cnstr(enode* n, sort* s) {
        if (!u.is_date(s) || is_attached_to_var(n))
            return;
        mk_var(n);
        push_axiom(n);
    }

    // The epoch map is injective: equal epochs imply equal dates.
    // Merged dates propagate their epoch and component equalities.
    // The axioms are deferred to unit_propagate.
    void solver::new_eq_eh(euf::th_eq const& eq) {
        expr* x = var2expr(eq.v1());
        expr* y = var2expr(eq.v2());
        expr* dx = nullptr, * dy = nullptr;
        if (u.is_epoch(x, dx) && u.is_epoch(y, dy) && dx != dy)
            push_link(dx, dy);
        if (u.is_date(x) && u.is_date(y) && x != y)
            push_link(x, y);
    }

    // Distinct dates have distinct epochs (and the full pair coupling).
    // The axioms are deferred to unit_propagate.
    void solver::new_diseq_eh(euf::th_eq const& eq) {
        expr* x = var2expr(eq.v1());
        expr* y = var2expr(eq.v2());
        if (!u.is_date(x) || !u.is_date(y) || x == y)
            return;
        push_link(x, y);
    }

    // --- model generation ------------------------------------------------

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (!u.is_date(n->get_expr())) {
            dep.insert(n, nullptr);
            return true;
        }
        enode* ep = nullptr;
        for (enode* sib : euf::enode_class(n)) {
            ep = get_epoch(sib);
            if (ep)
                break;
        }
        if (ep)
            dep.add(n, ep);
        else
            dep.insert(n, nullptr);
        return true;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(u.is_date(n->get_expr()));
        enode* ep = nullptr;
        for (enode* sib : euf::enode_class(n)) {
            ep = get_epoch(sib);
            if (ep)
                break;
        }
        rational val(0);
        bool has_val = false;
        if (ep) {
            expr* v = values.get(ep->get_root_id(), nullptr);
            has_val = v && u.arith().is_numeral(v, val);
        }
        if (!has_val) {
            val = m_next_fresh;
            m_next_fresh += rational::one();
        }
        values.set(n->get_root_id(), u.mk_value_from_epoch(val));
    }

    std::ostream& solver::display(std::ostream& out) const {
        for (unsigned v = 0; v < get_num_vars(); ++v)
            out << v << " -> " << mk_pp(var2expr(v), m) << "\n";
        return out;
    }

}
