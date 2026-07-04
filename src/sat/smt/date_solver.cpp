/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates (SAT/EUF core).

Author:

    Claude (Anthropic) 2026-07-04

--*/
#include "ast/ast_pp.h"
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_value.h"

namespace date {

    solver::solver(euf::solver& ctx, theory_id id):
        th_euf_solver(ctx, ctx.get_manager().get_family_name(id), id),
        m_util(ctx.get_manager()),
        m_arith(ctx.get_manager()),
        m_rewrite(ctx.get_manager()) {
        // normalize the date axioms so arithmetic atoms have the
        // (<= t numeral) shape expected by the arithmetic solver
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_rewrite.updt_params(p);
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx, get_id());
    }

    void solver::assert_axiom(expr* fml) {
        expr_ref f(fml, m);
        m_rewrite(f);
        if (m.is_true(f))
            return;
        add_unit(mk_literal(f));
    }

    void solver::ensure_axioms(expr* t) {
        SASSERT(is_date(t));
        if (m_axiomatized.contains(t))
            return;
        m_axiomatized.insert(t);
        ctx.push(insert_obj_trail<expr>(m_axiomatized, t));
        m_terms.push_back(t);
        ctx.push(push_back_vector<ptr_vector<expr>>(m_terms));
        if (u().is_add(t) || u().is_sub(t))
            ensure_axioms(to_app(t)->get_arg(0));
        rational vy, vm, vd;
        if (u().eval_ground(t, vy, vm, vd)) {
            // Concretely evaluated term: assert the exact component values
            // without simplification. The rewriter would fold the selector
            // applications away, losing the egraph link between the term
            // and its components.
            add_unit(eq_internalize(u().mk_year(t), m_arith.mk_int(vy)));
            add_unit(eq_internalize(u().mk_month(t), m_arith.mk_int(vm)));
            add_unit(eq_internalize(u().mk_day(t), m_arith.mk_int(vd)));
            return;
        }
        expr_ref_vector fmls(m);
        u().mk_term_spec(t, fmls);
        for (expr* f : fmls)
            assert_axiom(f);
    }

    void solver::internalize_cmp(app* atom) {
        literal lit = expr2literal(atom);
        expr_ref spec = u().mk_cmp_spec(atom->get_decl()->get_decl_kind(), atom->get_arg(0), atom->get_arg(1));
        m_rewrite(spec);
        if (m.is_true(spec)) {
            add_unit(lit);
            return;
        }
        if (m.is_false(spec)) {
            add_unit(~lit);
            return;
        }
        literal slit = mk_literal(spec);
        add_equiv(lit, slit);
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        auto lit = ctx.expr2literal(e);
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
            // foreign subterm: delegate to its own solver
            ctx.internalize(e);
            if (is_date(e)) {
                mk_var(expr2enode(e));
                ensure_axioms(e);
            }
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
            n = mk_enode(e);
        if (!n->is_attached_to(get_id()))
            mk_var(n);
        app* t = to_app(e);
        if (is_date(e))
            ensure_axioms(e);
        else if (u().is_comparison(e))
            internalize_cmp(t);
        else {
            // selector term: its date argument carries the axioms
            SASSERT(u().is_year(e) || u().is_month(e) || u().is_day(e));
            ensure_axioms(t->get_arg(0));
        }
        return true;
    }

    void solver::apply_sort_cnstr(enode* n, sort* s) {
        SASSERT(m_util.is_date(s));
        if (!n->is_attached_to(get_id()))
            mk_var(n);
        ensure_axioms(n->get_expr());
    }

    euf::theory_var solver::mk_var(enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        euf::theory_var r = th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, r);
        return r;
    }

    sat::check_result solver::check() {
        // Extensionality: two date terms whose components agree in the
        // arithmetic model must be equal. Instantiate the extensionality
        // lemma for pairs of candidate terms found in distinct classes.
        arith::arith_value av(ctx);
        obj_map<enode, expr*> root2term;
        for (expr* t : m_terms) {
            enode* n = expr2enode(t);
            if (!n)
                continue;
            enode* r = n->get_root();
            if (!root2term.contains(r))
                root2term.insert(r, t);
        }
        auto component_values = [&](expr* t, rational& y, rational& mo, rational& d) {
            expr_ref ye(u().mk_year(t), m), me(u().mk_month(t), m), de(u().mk_day(t), m);
            return
                expr2enode(ye) && av.get_value(ye, y) &&
                expr2enode(me) && av.get_value(me, mo) &&
                expr2enode(de) && av.get_value(de, d);
        };
        ptr_vector<expr> reps;
        for (auto const& kv : root2term)
            reps.push_back(kv.m_value);
        bool added = false;
        for (unsigned i = 0; i < reps.size(); ++i) {
            rational y1, m1, d1;
            if (!component_values(reps[i], y1, m1, d1))
                continue;
            for (unsigned j = i + 1; j < reps.size(); ++j) {
                rational y2, m2, d2;
                if (!component_values(reps[j], y2, m2, d2))
                    continue;
                if (y1 != y2 || m1 != m2 || d1 != d2)
                    continue;
                expr* a = reps[i], *b = reps[j];
                literal eq_y = eq_internalize(u().mk_year(a), u().mk_year(b));
                literal eq_m = eq_internalize(u().mk_month(a), u().mk_month(b));
                literal eq_d = eq_internalize(u().mk_day(a), u().mk_day(b));
                literal eq   = eq_internalize(a, b);
                add_clause(~eq_y, ~eq_m, ~eq_d, eq);
                added = true;
            }
        }
        return added ? sat::check_result::CR_CONTINUE : sat::check_result::CR_DONE;
    }

    expr* solver::find_axiomatized(enode* n) {
        for (enode* sib : euf::enode_class(n)) {
            expr* t = sib->get_expr();
            if (!m_axiomatized.contains(t))
                continue;
            expr_ref ye(u().mk_year(t), m), me(u().mk_month(t), m), de(u().mk_day(t), m);
            if (expr2enode(ye) && expr2enode(me) && expr2enode(de))
                return t;
        }
        return nullptr;
    }

    bool solver::add_dep(enode* n, top_sort<enode>& dep) {
        if (!is_date(n->get_expr()))
            return false;
        expr* t = find_axiomatized(n);
        if (!t) {
            dep.insert(n, nullptr);
            return true;
        }
        dep.add(n, expr2enode(u().mk_year(t))->get_root());
        dep.add(n, expr2enode(u().mk_month(t))->get_root());
        dep.add(n, expr2enode(u().mk_day(t))->get_root());
        return true;
    }

    void solver::add_value(enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(is_date(n->get_expr()));
        expr* t = find_axiomatized(n);
        rational y, mo, d;
        if (t &&
            m_arith.is_numeral(values.get(expr2enode(u().mk_year(t))->get_root_id()), y) &&
            m_arith.is_numeral(values.get(expr2enode(u().mk_month(t))->get_root_id()), mo) &&
            m_arith.is_numeral(values.get(expr2enode(u().mk_day(t))->get_root_id()), d) &&
            date_util::is_valid_date(y, mo, d)) {
            values.set(n->get_root_id(), u().mk_date(y, mo, d));
            return;
        }
        values.set(n->get_root_id(), u().mk_date(rational(1970), rational(1), rational(1)));
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "date solver:\n";
        for (expr* t : m_terms)
            out << mk_bounded_pp(t, m, 2) << "\n";
        return out;
    }
}
