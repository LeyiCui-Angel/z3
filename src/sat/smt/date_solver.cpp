/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates in the SAT/EUF pipeline.

Author:

    Date theory extension 2026-07-05

--*/
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"
#include "model/date_factory.h"

namespace date {

    solver::solver(euf::solver& ctx, euf::theory_id id):
        th_euf_solver(ctx, symbol("date"), id),
        u(m),
        a(m),
        m_rw(m),
        m_ax(m, [this](expr_ref_vector const& lits) { add_axiom_clause(lits); }) {
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx, get_id());
    }

    void solver::add_axiom_clause(expr_ref_vector const& lits) {
        sat::literal_vector ls;
        for (expr* e : lits) {
            // normalize the literal: the arithmetic solver expects
            // simplified atoms. Date comparison atoms are kept as is:
            // they define themselves through these clauses.
            expr* pos = e;
            m.is_not(e, pos);
            expr_ref r(e, m);
            if (!u.is_lt(pos) && !u.is_le(pos) && !u.is_gt(pos) && !u.is_ge(pos))
                m_rw(r);
            if (m.is_true(r))
                return;
            if (m.is_false(r))
                continue;
            ls.push_back(mk_literal(r));
        }
        add_clause(ls);
    }

    void solver::ensure_axioms(expr* e) {
        SASSERT(u.is_date(e));
        if (m_axiomatized.contains(e))
            return;
        m_axiomatized.insert(e);
        ctx.push(insert_obj_trail<expr>(m_axiomatized, e));
        // If the term simplifies (e.g. date.sub to date.add, or concrete
        // evaluation), link it to its simplified form and axiomatize that
        // form instead. The axioms below would otherwise be rewritten away
        // from this term when their literals are normalized.
        expr_ref r(e, m);
        m_rw(r);
        if (r.get() != e) {
            add_unit(mk_literal(m.mk_eq(e, r)));
            return;
        }
        // For concrete valid constructor values pin the selectors directly:
        // the guarded selector axioms would be folded away by normalization
        // without ever creating the selector terms.
        rational vy, vm, vd;
        if (u.is_date_value(e, vy, vm, vd)) {
            add_unit(mk_literal(m.mk_eq(u.mk_year(e), a.mk_int(vy))));
            add_unit(mk_literal(m.mk_eq(u.mk_month(e), a.mk_int(vm))));
            add_unit(mk_literal(m.mk_eq(u.mk_day(e), a.mk_int(vd))));
            return;
        }
        m_ax.date_term_axioms(e);
        if (u.is_mk(e))
            m_ax.mk_axioms(to_app(e));
        else if (u.is_add(e) || u.is_sub(e))
            m_ax.add_axioms(to_app(e));
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        force_push();
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        sat::literal lit = expr2literal(e);
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
            n = mk_enode(e);
        if (!n->is_attached_to(get_id()))
            mk_var(n);
        if (u.is_lt(e) || u.is_le(e) || u.is_gt(e) || u.is_ge(e))
            m_ax.cmp_axioms(to_app(e));
        // apply_sort_cnstr is only invoked for terms whose function does not
        // belong to this theory, so constructor and arithmetic terms are
        // axiomatized here
        if (u.is_date(e))
            ensure_axioms(e);
        return true;
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        euf::theory_var r = th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, r);
        return r;
    }

    void solver::apply_sort_cnstr(euf::enode* n, sort* s) {
        SASSERT(u.is_date(s));
        force_push();
        if (!is_attached_to_var(n))
            mk_var(n);
        ensure_axioms(n->get_expr());
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "date solver\n";
        return out;
    }

    // Search the equivalence class of n for a concrete date value, or
    // failing that, a member whose selector terms have been internalized.
    expr* solver::value_source(euf::enode* n, enode*& yn, enode*& mon, enode*& dn) {
        yn = mon = dn = nullptr;
        rational y, mo, d;
        for (enode* sib : euf::enode_class(n)) {
            expr* se = sib->get_expr();
            if (u.is_date_value(se, y, mo, d))
                return se;
            if (!yn) {
                enode* yn1  = expr2enode(u.mk_year(se));
                enode* mon1 = expr2enode(u.mk_month(se));
                enode* dn1  = expr2enode(u.mk_day(se));
                if (yn1 && mon1 && dn1) {
                    yn = yn1; mon = mon1; dn = dn1;
                }
            }
        }
        return nullptr;
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        expr* e = n->get_expr();
        if (!u.is_date(e)) {
            dep.insert(n, nullptr);
            return true;
        }
        enode* yn = nullptr, *mon = nullptr, *dn = nullptr;
        if (!value_source(n, yn, mon, dn) && yn) {
            dep.add(n, yn->get_root());
            dep.add(n, mon->get_root());
            dep.add(n, dn->get_root());
        }
        else
            dep.insert(n, nullptr);
        return true;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        expr* e = n->get_expr();
        SASSERT(u.is_date(e));
        enode* yn = nullptr, *mon = nullptr, *dn = nullptr;
        expr* val = value_source(n, yn, mon, dn);
        rational y, mo, d;
        if (val) {
            values.set(n->get_root_id(), val);
            return;
        }
        if (yn && mon && dn &&
            a.is_numeral(values.get(yn->get_root_id()), y) &&
            a.is_numeral(values.get(mon->get_root_id()), mo) &&
            a.is_numeral(values.get(dn->get_root_id()), d) &&
            date_util::is_valid_date(y, mo, d)) {
            values.set(n->get_root_id(), u.mk_date_value(y, mo, d));
            return;
        }
        // unconstrained date; any valid date will do
        values.set(n->get_root_id(), u.plugin().get_some_value(e->get_sort()));
    }
}
