/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates for the SAT/EUF core.

Author:

    Date theory extension 2026-07-05

--*/
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"
#include "ast/ast_pp.h"

namespace date {

    solver::solver(euf::solver& ctx, euf::theory_id id):
        th_euf_solver(ctx, symbol("date"), id),
        m_util(m),
        m_rewrite(m),
        m_atoms(m),
        m_rhs(m),
        m_generated_refs(m) {
        // normalize arithmetic atoms into "term <= numeral" form; the
        // arithmetic solver does not handle other inequality shapes
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_rewrite.updt_params(p);
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx, get_id());
    }

    void solver::queue_axiom(expr* e) {
        queue_equiv(nullptr, e);
    }

    // for axioms already in final form, which simplification would fold away
    // (e.g. selector equations on concrete constructor applications)
    void solver::queue_no_rewrite(expr* e) {
        queue_equiv(e, m.mk_true());
    }

    void solver::queue_equiv(expr* atom, expr* rhs) {
        m_atoms.push_back(atom);
        ctx.push(push_back_vector<expr_ref_vector>(m_atoms));
        m_rhs.push_back(rhs);
        ctx.push(push_back_vector<expr_ref_vector>(m_rhs));
    }

    void solver::assert_axiom(expr* atom, expr* rhs) {
        // normalize the asserted formula; the theory solvers (notably
        // arithmetic) expect atoms in simplified form. The date atom of an
        // equivalence is kept as is: the rewriter could change gt/ge atoms
        // into their lt/le mirror.
        expr_ref r(rhs, m);
        m_rewrite(r);
        TRACE(date, tout << "assert: " << mk_pp(atom, m) << " == " << r << "\n";);
        if (!atom) {
            if (!m.is_true(r))
                add_unit(mk_literal(r));
            return;
        }
        sat::literal alit = mk_literal(atom);
        if (m.is_true(r)) {
            add_unit(alit);
            return;
        }
        if (m.is_false(r)) {
            add_unit(~alit);
            return;
        }
        sat::literal rlit = mk_literal(r);
        add_clause(~alit, rlit);
        add_clause(alit, ~rlit);
    }

    /**
       \brief The axioms constrain a term through its selector applications.
       If the term is not in rewriter normal form, the rewriting pass over
       the axioms would displace the selectors onto the normal form, leaving
       the original term unconstrained. Instead, link the term to its normal
       form (which then receives the axioms) with a plain equality.
       Returns true if the term was linked.
    */
    bool solver::link_normal_form(expr* e) {
        expr_ref norm(e, m);
        m_rewrite(norm);
        if (norm == e)
            return false;
        if (!m_linked.contains(e)) {
            m_linked.insert(e);
            ctx.push(insert_obj_trail<expr>(m_linked, e));
            queue_no_rewrite(m.mk_eq(e, norm));
        }
        return true;
    }

    /**
       \brief Instantiate the axioms shared by every term of sort Date:
       validity of the selector triple, the reconstruction identity, and
       the epoch-day link.
    */
    void solver::add_date_term_axioms(expr* e) {
        if (m_term_axiomatized.contains(e) || m_generated.contains(e))
            return;
        m_term_axiomatized.insert(e);
        ctx.push(insert_obj_trail<expr>(m_term_axiomatized, e));
        if (link_normal_form(e))
            return;
        expr_ref_vector axioms(m);
        expr_ref recon(m);
        m_util.mk_date_term_axioms(e, axioms, recon);
        // the reconstruction term is definitionally equal to e; do not
        // instantiate date-term axioms for it again
        if (!m_generated.contains(recon)) {
            m_generated.insert(recon);
            m_generated_refs.push_back(recon);
        }
        for (expr* ax : axioms)
            queue_axiom(ax);
    }

    void solver::add_op_axioms(app* term) {
        if (m_op_axiomatized.contains(term) || m_generated.contains(term))
            return;
        m_op_axiomatized.insert(term);
        ctx.push(insert_obj_trail<expr>(m_op_axiomatized, term));
        if (link_normal_form(term))
            return;
        if (m_util.is_mk(term)) {
            expr_ref_vector axioms(m);
            bool concrete = m_util.mk_constructor_axioms(term, axioms);
            for (expr* ax : axioms)
                concrete ? queue_no_rewrite(ax) : queue_axiom(ax);
        }
        else if (m_util.is_add(term) || m_util.is_sub(term)) {
            bool concrete = false;
            expr_ref ax = m_util.mk_add_axiom(term, concrete);
            concrete ? queue_no_rewrite(ax) : queue_axiom(ax);
            // eager epoch injectivity between the result and its base;
            // resolves identities such as date.add(d,0,0,0) = d at the
            // boolean level
            queue_axiom(m_util.mk_diseq_axiom(term, term->get_arg(0)));
        }
        else if (m_util.is_lt(term) || m_util.is_le(term) || m_util.is_gt(term) || m_util.is_ge(term))
            queue_equiv(term, m_util.mk_compare_rhs(term));
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        force_push();
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        auto lit = expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e) {
        force_push();
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
        if (!n->is_attached_to(get_id())) {
            euf::theory_var w = mk_var(n);
            ctx.attach_th_var(n, this, w);
        }
        add_op_axioms(to_app(e));
        if (m_util.is_date(e))
            add_date_term_axioms(e);
        return true;
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        return th_euf_solver::mk_var(n);
    }

    void solver::apply_sort_cnstr(euf::enode* n, sort* s) {
        SASSERT(m_util.is_date(s));
        force_push();
        if (!is_attached_to_var(n)) {
            euf::theory_var w = mk_var(n);
            ctx.attach_th_var(n, this, w);
        }
        add_date_term_axioms(n->get_expr());
    }

    void solver::new_diseq_eh(euf::th_eq const& eq) {
        expr* e1 = var2expr(eq.v1());
        expr* e2 = var2expr(eq.v2());
        if (!m_util.is_date(e1))
            return;
        queue_axiom(m_util.mk_diseq_axiom(e1, e2));
    }

    bool solver::unit_propagate() {
        force_push();
        if (m_qhead == m_rhs.size())
            return false;
        ctx.push(value_trail<unsigned>(m_qhead));
        for (; m_qhead < m_rhs.size() && !s().inconsistent(); ++m_qhead) {
            expr_ref atom(m_atoms.get(m_qhead), m);
            expr_ref rhs(m_rhs.get(m_qhead), m);
            assert_axiom(atom, rhs);
        }
        return true;
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out << "theory date\n";
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(m_util.is_date(n->get_expr()));
        // find a member of the class whose selector terms are internalized
        for (euf::enode* it : euf::enode_class(n)) {
            expr* e = it->get_expr();
            app_ref y(m_util.mk_year(e), m), mo(m_util.mk_month(e), m), d(m_util.mk_day(e), m);
            euf::enode* ny = expr2enode(y);
            euf::enode* nmo = expr2enode(mo);
            euf::enode* nd = expr2enode(d);
            if (ny && nmo && nd) {
                expr* vy = values.get(ny->get_root_id());
                expr* vmo = values.get(nmo->get_root_id());
                expr* vd = values.get(nd->get_root_id());
                if (vy && vmo && vd) {
                    values.set(n->get_root_id(), m_util.mk_date(vy, vmo, vd));
                    return;
                }
            }
        }
        values.set(n->get_root_id(), m_util.mk_date(rational(1), rational(1), rational(1)));
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (!m_util.is_date(n->get_expr()))
            return false;
        bool added = false;
        for (euf::enode* it : euf::enode_class(n)) {
            expr* e = it->get_expr();
            app_ref y(m_util.mk_year(e), m), mo(m_util.mk_month(e), m), d(m_util.mk_day(e), m);
            euf::enode* ny = expr2enode(y);
            euf::enode* nmo = expr2enode(mo);
            euf::enode* nd = expr2enode(d);
            if (ny && nmo && nd) {
                dep.add(n, ny->get_root());
                dep.add(n, nmo->get_root());
                dep.add(n, nd->get_root());
                added = true;
                break;
            }
        }
        if (!added)
            dep.insert(n, nullptr);
        return true;
    }
}
