/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates (SAT/EUF pipeline).

Author:

    Claude 2026-07-05

--*/
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"
#include "ast/ast_pp.h"

namespace date {

    solver::solver(euf::solver& ctx, theory_id id):
        th_euf_solver(ctx, ctx.get_manager().get_family_name(id), id),
        dt(m),
        a(m),
        ax(m),
        m_axioms(m),
        m_dates(m) {
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx, get_id());
    }

    void solver::push_axiom(expr* e) {
        // The axiom is asserted as constructed: simplifying it here could
        // rewrite away the date terms it is meant to constrain (e.g.
        // (date.add d 0 0 0) folds to d), detaching the axiom from the
        // enodes of the original goal.
        m_axioms.push_back(e);
    }

    void solver::add_date_term(app* t) {
        SASSERT(dt.is_date(t));
        enode* n = expr2enode(t);
        if (!n)
            n = e_internalize(t);
        mk_var(n);
        if (m_seen.contains(t))
            return;
        m_seen.insert(t);
        // Every Date term denotes a calendar-valid date ...
        push_axiom(ax.valid_axiom(t));
        // ... and is reconstructed from its selectors (except date.mk
        // applications, where reconstruction follows from the selector
        // axioms and would otherwise not terminate).
        if (!dt.is_mk(t))
            push_axiom(ax.recon_axiom(t));
        // Defining axioms of the date operations.
        if (dt.is_mk(t))
            push_axiom(ax.mk_axiom(t));
        else if (dt.is_add(t) || dt.is_sub(t)) {
            push_axiom(ax.add_axiom(t));
            if (is_app(t->get_arg(0)))
                add_date_term(to_app(t->get_arg(0)));
        }
        // Equality and order agree with the Rata Die day numbers.
        for (expr* other : m_dates)
            push_axiom(ax.bridge_axiom(t, other));
        m_dates.push_back(t);
    }

    bool solver::unit_propagate() {
        if (m_axioms_qhead == m_axioms.size())
            return false;
        ctx.push(value_trail<unsigned>(m_axioms_qhead));
        for (; m_axioms_qhead < m_axioms.size(); ++m_axioms_qhead) {
            expr_ref e(m_axioms.get(m_axioms_qhead), m);
            TRACE(theory_date, tout << "assert: " << e << "\n";);
            add_unit(mk_literal(e));
        }
        return true;
    }

    sat::check_result solver::check() {
        return m_axioms_qhead < m_axioms.size() ? sat::check_result::CR_CONTINUE : sat::check_result::CR_DONE;
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
            ctx.internalize(e);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;
    }

    bool solver::visited(expr* e) {
        enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        enode* n = expr2enode(e);
        if (!n)
            n = mk_enode(e);
        SASSERT(!n->is_attached_to(get_id()));
        mk_var(n);
        app* t = to_app(e);
        switch (t->get_decl_kind()) {
        case OP_DATE_MK:
        case OP_DATE_ADD:
        case OP_DATE_SUB:
            add_date_term(t);
            break;
        case OP_DATE_YEAR:
        case OP_DATE_MONTH:
        case OP_DATE_DAY:
            if (is_app(t->get_arg(0)))
                add_date_term(to_app(t->get_arg(0)));
            break;
        case OP_DATE_LT:
        case OP_DATE_LE:
        case OP_DATE_GT:
        case OP_DATE_GE:
            for (expr* arg : *t)
                if (is_app(arg))
                    add_date_term(to_app(arg));
            push_axiom(ax.cmp_axiom(t));
            break;
        default:
            break;
        }
        return true;
    }

    void solver::apply_sort_cnstr(enode* n, sort* s) {
        SASSERT(dt.is_date(s));
        if (is_app(n->get_expr()))
            add_date_term(to_app(n->get_expr()));
    }

    euf::theory_var solver::mk_var(enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        euf::theory_var r = th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, r);
        return r;
    }

    bool solver::find_triple(enode* n, enode*& y, enode*& mo, enode*& d) {
        for (enode* sib : euf::enode_class(n)) {
            expr* e = sib->get_expr();
            if (!dt.is_date(e))
                continue;
            enode* ny = expr2enode(dt.mk_year(e));
            enode* nm = expr2enode(dt.mk_month(e));
            enode* nd = expr2enode(dt.mk_day(e));
            if (ny && nm && nd) {
                y = ny; mo = nm; d = nd;
                return true;
            }
        }
        return false;
    }

    bool solver::add_dep(enode* n, top_sort<enode>& dep) {
        if (!dt.is_date(n->get_expr()))
            return false;
        enode* y, * mo, * d;
        if (find_triple(n, y, mo, d)) {
            dep.add(n, y->get_root());
            dep.add(n, mo->get_root());
            dep.add(n, d->get_root());
        }
        else
            dep.insert(n, nullptr);
        return true;
    }

    void solver::add_value(enode* n, model& mdl, expr_ref_vector& values) {
        enode* y, * mo, * d;
        rational ry, rm, rd;
        if (find_triple(n, y, mo, d)) {
            expr* vy = values.get(y->get_root_id(), nullptr);
            expr* vm = values.get(mo->get_root_id(), nullptr);
            expr* vd = values.get(d->get_root_id(), nullptr);
            if (vy && vm && vd &&
                a.is_numeral(vy, ry) && a.is_numeral(vm, rm) && a.is_numeral(vd, rd) &&
                date_decl_plugin::is_valid_date(ry, rm, rd)) {
                values.set(n->get_root_id(), dt.mk_date(ry, rm, rd));
                return;
            }
        }
        // The validity axioms guarantee well-formed selector values;
        // fall back to an arbitrary date if they are unavailable.
        values.set(n->get_root_id(), dt.mk_date(rational(1), rational(1), rational(1)));
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "date solver\n";
        for (expr* d : m_dates)
            out << mk_pp(d, m) << "\n";
        return out;
    }
}
