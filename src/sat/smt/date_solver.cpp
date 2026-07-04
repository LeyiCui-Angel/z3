/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    SAT/EUF theory solver for the native theory of calendar dates.
    See date_solver.h, ast/date_axioms.h and Dates.smt2.

Author:

    Angel Cui 2026

--*/

#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"

namespace date {

    solver::solver(euf::solver& ctx, theory_id id) :
        th_euf_solver(ctx, ctx.get_manager().get_family_name(id), id),
        du(m),
        m_gen(m),
        m_th_rw(m),
        m_axioms(m) {
    }

    // ----- internalization -------------------------------------------------

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

    bool solver::visit(expr* e) {
        if (visited(e))
            return true;
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e);   // hand foreign (Int/Bool) subterms to the core
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        if (!n)
            n = mk_enode(e, false);
        if (n->is_attached_to(get_id()))
            return true;
        mk_var(n);
        m_nodes.push_back(std::tuple(n, sign, root));
        ctx.push(push_back_trail(m_nodes));
        return true;
    }

    euf::theory_var solver::mk_var(enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        euf::theory_var v = th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, v);
        return v;
    }

    void solver::apply_sort_cnstr(enode* n, sort* s) {
        if (!du.is_date_sort(s) || n->is_attached_to(get_id()))
            return;
        mk_var(n);
        m_nodes.push_back(std::tuple(n, false, false));
        ctx.push(push_back_trail(m_nodes));
    }

    // ----- axiom emission (deferred to propagation, level-safe) ------------

    bool solver::unit_propagate() {
        if (m_nodes_qhead >= m_nodes.size())
            return false;
        ctx.push(value_trail<unsigned>(m_nodes_qhead));
        for (; m_nodes_qhead < m_nodes.size(); ++m_nodes_qhead)
            reduce(std::get<0>(m_nodes[m_nodes_qhead]));
        return true;
    }

    void solver::reduce(enode* n) {
        expr* e = n->get_expr();
        if (m_processed.contains(e))
            return;
        m_processed.insert(e);
        if (du.is_date(e))
            m_gen.reduce_term(e, m_axioms);
        else if (du.is_lt(e) || du.is_le(e) || du.is_gt(e) || du.is_ge(e))
            m_gen.reduce_atom(to_app(e), m_axioms);
        else
            return;                 // date.year/month/day: no defining axiom
        flush_axioms();
    }

    void solver::flush_axioms() {
        while (!m_axioms.empty()) {
            expr_ref_vector batch(m);
            batch.swap(m_axioms);
            for (expr* e0 : batch) {
                expr_ref e(e0, m);
                m_th_rw(e);
                if (m.is_true(e))
                    continue;
                add_unit(mk_literal(e));
            }
        }
    }

    // ----- model construction ----------------------------------------------

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        expr* e = n->get_expr();
        if (!du.is_date(e))
            return false;
        enode* yn = expr2enode(du.mk_year(e));
        enode* mn = expr2enode(du.mk_month(e));
        enode* dn = expr2enode(du.mk_day(e));
        if (yn && mn && dn) {
            dep.add(n, yn->get_root());
            dep.add(n, mn->get_root());
            dep.add(n, dn->get_root());
        }
        else
            dep.insert(n, nullptr);
        return true;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        expr* e = n->get_expr();
        enode* yn = expr2enode(du.mk_year(e));
        enode* mn = expr2enode(du.mk_month(e));
        enode* dn = expr2enode(du.mk_day(e));
        if (yn && mn && dn) {
            expr* yv = values.get(yn->get_root_id());
            expr* mv = values.get(mn->get_root_id());
            expr* dv = values.get(dn->get_root_id());
            if (yv && mv && dv) {
                values.set(n->get_root_id(), du.mk_mk(yv, mv, dv));
                return;
            }
        }
        values.set(n->get_root_id(), to_app(du.plugin().get_some_value(n->get_sort())));
    }
}
