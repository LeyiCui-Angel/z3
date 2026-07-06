/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for the Dates theory in the SAT/EUF core.

Author:

    Date theory extension 2026-07-04

--*/
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"

namespace dates {

    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, symbol("date"), ctx.get_manager().mk_family_id("date")),
        dt(m),
        a(m),
        m_ax(m),
        m_rw(m) {
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_rw.updt_params(p);
        m_ax.set_add_axiom([this](expr* e) { assert_axiom(e); });
        m_ax.set_add_eq([this](expr* a, expr* b) { assert_eq(a, b); });
        m_ax.set_add_iff([this](expr* atom, expr* def) { assert_iff(atom, def); });
    }

    void solver::assert_axiom(expr* e) {
        expr_ref fml(e, m);
        // normalize arithmetic atoms into the form the arithmetic
        // solver internalizes
        m_rw(fml);
        if (m.is_true(fml))
            return;
        TRACE(date, tout << "assert: " << fml << "\n";);
        add_unit(mk_literal(fml));
    }

    // Definitional equality. Both sides are internalized verbatim: the
    // left-hand side anchors selector and epoch terms of a Date e-graph
    // node, so it must not be folded by the rewriter.
    void solver::assert_eq(expr* a, expr* b) {
        // normalize embedded arithmetic atoms on the definition side only
        expr_ref bn(b, m);
        m_rw(bn);
        TRACE(date, tout << "assert: " << mk_pp(a, m) << " = " << bn << "\n";);
        add_unit(eq_internalize(a, bn));
    }

    // Definition of a comparison atom. The atom keeps its literal; only
    // the definition side is normalized.
    void solver::assert_iff(expr* atom, expr* def) {
        expr_ref d(def, m);
        m_rw(d);
        TRACE(date, tout << "assert: " << mk_pp(atom, m) << " <=> " << d << "\n";);
        sat::literal la = mk_literal(atom);
        if (m.is_true(d)) {
            add_unit(la);
            return;
        }
        if (m.is_false(d)) {
            add_unit(~la);
            return;
        }
        sat::literal ld = mk_literal(d);
        add_clause(~la, ld);
        add_clause(la, ~ld);
    }

    void solver::push_queue(expr* e) {
        m_queue.push_back(e);
        ctx.push(push_back_trail(m_queue));
    }

    // Track a Date-sorted enode: attach a theory variable (used for model
    // construction) and schedule its defining axioms.
    void solver::track(euf::enode* n) {
        if (n->is_attached_to(get_id()))
            return;
        SASSERT(dt.is_date(n->get_expr()));
        euf::theory_var v = mk_var(n);
        ctx.attach_th_var(n, this, v);
        push_queue(n->get_expr());
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
        if (!n)
            n = mk_enode(e, false);
        SASSERT(!n->is_attached_to(get_id()));
        if (dt.is_date(e))
            track(n);
        else {
            euf::theory_var v = mk_var(n);
            ctx.attach_th_var(n, this, v);
            if (dt.is_comparison(e)) {
                for (expr* arg : *to_app(e))
                    track(expr2enode(arg));
                push_queue(e);
            }
            else {
                // selector applications; the argument carries the axioms
                SASSERT(dt.is_selector(e));
                track(expr2enode(to_app(e)->get_arg(0)));
            }
        }
        return true;
    }

    void solver::apply_sort_cnstr(euf::enode* n, sort* s) {
        SASSERT(dt.is_date(s));
        track(n);
    }

    void solver::new_diseq_eh(euf::th_eq const& eq) {
        ctx.push(push_back_trail(m_diseqs));
        m_diseqs.push_back({eq.v1(), eq.v2()});
    }

    // Instantiating axioms internalizes new terms, which can grow the
    // queues while they are drained; the loop conditions re-read the sizes.
    bool solver::flush_axioms() {
        if (m_qhead >= m_queue.size() && m_dhead >= m_diseqs.size())
            return false;
        while (m_qhead < m_queue.size() || m_dhead < m_diseqs.size()) {
            if (m_qhead < m_queue.size()) {
                ctx.push(value_trail<unsigned>(m_qhead));
                expr* e = m_queue[m_qhead++];
                if (dt.is_comparison(e))
                    m_ax.compare_axioms(to_app(e));
                else
                    m_ax.term_axioms(e);
            }
            else {
                ctx.push(value_trail<unsigned>(m_dhead));
                auto [v1, v2] = m_diseqs[m_dhead++];
                m_ax.diseq_axiom(var2expr(v1), var2expr(v2));
            }
        }
        return true;
    }

    bool solver::unit_propagate() {
        return flush_axioms();
    }

    sat::check_result solver::check() {
        if (flush_axioms())
            return sat::check_result::CR_CONTINUE;
        return sat::check_result::CR_DONE;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        expr* t = n->get_expr();
        rational num[3] = { rational(1), rational(1), rational(1) };
        expr_ref sel[3] = { expr_ref(dt.mk_year(t), m), expr_ref(dt.mk_month(t), m), expr_ref(dt.mk_day(t), m) };
        for (unsigned i = 0; i < 3; ++i) {
            euf::enode* sn = expr2enode(sel[i]);
            expr* v = sn ? values.get(sn->get_root_id(), nullptr) : nullptr;
            if (v)
                a.is_numeral(v, num[i]);
        }
        values.set(n->get_root_id(), dt.mk_mk(num[0], num[1], num[2]));
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        expr* t = n->get_expr();
        expr_ref sel[3] = { expr_ref(dt.mk_year(t), m), expr_ref(dt.mk_month(t), m), expr_ref(dt.mk_day(t), m) };
        bool has_dep = false;
        for (auto const& s : sel) {
            euf::enode* sn = expr2enode(s);
            if (sn) {
                dep.add(n, sn);
                has_dep = true;
            }
        }
        if (!has_dep)
            dep.insert(n, nullptr);
        return true;
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "date solver:\n";
        for (unsigned v = 0; v < get_num_vars(); ++v)
            out << v << " -> " << mk_bounded_pp(var2expr(v), m) << "\n";
        return out;
    }
}
