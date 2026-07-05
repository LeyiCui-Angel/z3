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

    bool solver::unit_propagate() {
        if (m_qhead == m_axiom_queue.size())
            return false;
        ctx.push(value_trail<unsigned>(m_qhead));
        for (; m_qhead < m_axiom_queue.size(); ++m_qhead)
            axiomatize(m_axiom_queue[m_qhead]);
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
    void solver::ensure_rep(enode* n) {
        SASSERT(u.is_date(n->get_expr()));
        theory_var v = mk_var(n);
        if (m_var2rep[v].m_epoch)
            return;
        app* t = to_app(n->get_expr());
        expr_ref ep(u.mk_epoch(t), m);
        ctx.internalize(ep);
        var_rep& rep = m_var2rep[v];
        rep.m_epoch = expr2enode(ep);
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
            add_axiom_eq(ep, a.mk_numeral(en, true));
            return;
        }

        expr_ref_vector fmls(m);
        expr_ref y(m), mo(m), d(m);
        expr_ref civil_epoch = u.mk_civil_rep(y, mo, d, fmls);
        rep.m_year = y;
        rep.m_month = mo;
        rep.m_day = d;
        m_trail.push_back(y);
        m_trail.push_back(mo);
        m_trail.push_back(d);
        add_axiom_eq(ep, civil_epoch);

        if (u.is_mk(t))
            add_axiom_eq(ep, u.mk_epoch_of_ymd(t->get_arg(0), t->get_arg(1), t->get_arg(2), fmls));
        else if (u.is_add(t) || u.is_sub(t)) {
            enode* arg = expr2enode(t->get_arg(0));
            ensure_rep(arg);
            expr_ref ep0(u.mk_epoch(t->get_arg(0)), m);
            rational rpy, rpm;
            if (a.is_numeral(t->get_arg(1), rpy) && rpy.is_zero() &&
                a.is_numeral(t->get_arg(2), rpm) && rpm.is_zero()) {
                // pure day offsets shift the epoch directly: with a zero month
                // offset the day clamp is the identity
                expr* pd = t->get_arg(3);
                add_axiom_eq(ep, u.is_sub(t) ? a.mk_sub(ep0, pd) : a.mk_add(ep0, pd));
            }
            else {
                var_rep const& arep = m_var2rep[arg->get_th_var(get_id())];
                add_axiom_eq(ep, u.mk_epoch_add(arep.m_year, arep.m_month, arep.m_day,
                                                t->get_arg(1), t->get_arg(2), t->get_arg(3),
                                                u.is_sub(t), fmls));
            }
        }
        add_axioms(fmls);
    }

    void solver::axiomatize(enode* n) {
        expr* e = n->get_expr();
        if (u.is_date(e)) {
            ensure_rep(n);
            return;
        }
        app* t = to_app(e);
        if (u.is_year(e) || u.is_month(e) || u.is_day(e)) {
            enode* arg = expr2enode(t->get_arg(0));
            ensure_rep(arg);
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
            ensure_rep(expr2enode(x));
            ensure_rep(expr2enode(yy));
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
            return;
        }
        // date.epoch terms carry no axioms of their own
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
    void solver::new_eq_eh(euf::th_eq const& eq) {
        expr* x = var2expr(eq.v1());
        expr* y = var2expr(eq.v2());
        expr* dx = nullptr, * dy = nullptr;
        if (u.is_epoch(x, dx) && u.is_epoch(y, dy) && dx != dy)
            add_clause(~eq_internalize(x, y), eq_internalize(dx, dy));
    }

    // Distinct dates have distinct epochs.
    void solver::new_diseq_eh(euf::th_eq const& eq) {
        expr* x = var2expr(eq.v1());
        expr* y = var2expr(eq.v2());
        if (!u.is_date(x) || !u.is_date(y))
            return;
        expr_ref epx(u.mk_epoch(x), m), epy(u.mk_epoch(y), m);
        add_clause(eq_internalize(x, y), ~eq_internalize(epx, epy));
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
