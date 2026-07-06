/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates for the SAT/EUF core.

Author:

    Angel Cui 2026-03-23

--*/

#include "ast/ast_pp.h"
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"

namespace date {

    solver::solver(euf::solver& ctx, euf::theory_id id) :
        th_euf_solver(ctx, symbol("date"), id),
        u(m),
        a(m),
        m_rw(m),
        m_diseq_trail(m) {
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_rw.updt_params(p);
    }

    void solver::attach_new_th_var(enode* n) {
        theory_var v = mk_var(n);
        ctx.attach_th_var(n, this, v);
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
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n)
            n = mk_enode(e);
        attach_new_th_var(n);
        m_nodes.push_back(n);
        ctx.push(push_back_trail(m_nodes));
        return true;
    }

    void solver::apply_sort_cnstr(euf::enode* n, sort* s) {
        SASSERT(u.is_date(s));
        if (is_attached_to_var(n))
            return;
        attach_new_th_var(n);
        m_nodes.push_back(n);
        ctx.push(push_back_trail(m_nodes));
    }

    bool solver::unit_propagate() {
        if (m_nodes_qhead >= m_nodes.size())
            return false;
        ctx.push(value_trail<unsigned>(m_nodes_qhead));
        for (; m_nodes_qhead < m_nodes.size(); ++m_nodes_qhead)
            add_axioms(m_nodes[m_nodes_qhead]);
        return true;
    }

    sat::check_result solver::check() {
        if (unit_propagate())
            return sat::check_result::CR_CONTINUE;
        return sat::check_result::CR_DONE;
    }

    void solver::add_axioms(enode* n) {
        expr* e = n->get_expr();
        if (m.is_bool(e)) {
            add_cmp_axioms(to_app(e));
            return;
        }
        // reconstruction terms (date.mk (date.year s) ...) need no axioms of
        // their own: the identity s = t asserted for s makes all their
        // properties available through congruence, and a second copy of the
        // validity constraints only burdens the arithmetic solver
        if (u.is_selector_mk(e))
            return;
        if (u.is_date(e))
            add_date_axioms(e);
        if (u.is_mk(e))
            add_mk_axioms(to_app(e));
        else if (u.is_add(e))
            add_arith_axioms(to_app(e), false);
        else if (u.is_sub(e))
            add_arith_axioms(to_app(e), true);
    }

    void solver::assert_unit(expr* e) {
        expr_ref f(e, m);
        m_rw(f);
        if (m.is_true(f))
            return;
        add_unit(mk_literal(f));
    }

    // assert e verbatim, without running the rewriter: used for selector
    // equations of concrete constructor applications, where the rewriter
    // would fold the selector term away and leave no enode for congruence
    void solver::assert_unit_norewrite(expr* e) {
        add_unit(mk_literal(e));
    }

    void solver::assert_implies(expr* premise, expr* conseq) {
        expr_ref p(premise, m), c(conseq, m);
        m_rw(p);
        m_rw(c);
        if (m.is_false(p) || m.is_true(c))
            return;
        if (m.is_true(p)) {
            assert_unit(c);
            return;
        }
        add_clause(~mk_literal(p), mk_literal(c));
    }

    void solver::assert_iff(literal lit, expr* def) {
        expr_ref d(def, m);
        m_rw(d);
        if (m.is_true(d)) {
            add_unit(lit);
            return;
        }
        if (m.is_false(d)) {
            add_unit(~lit);
            return;
        }
        add_equiv(lit, mk_literal(d));
    }

    expr* solver::mk_neg(expr* e) {
        rational r;
        if (a.is_numeral(e, r))
            return a.mk_numeral(-r, true);
        return a.mk_uminus(e);
    }

    expr_ref solver::mk_rata_die(expr* d) {
        return u.mk_rata_die(u.mk_year(d), u.mk_month(d), u.mk_day(d));
    }

    // phase preference, not an axiom: try to place years in the familiar
    // calendar range first, so that unconstrained dates receive natural
    // model values; out-of-range years remain reachable when required
    void solver::add_year_range_preference(expr* y) {
        expr_ref lo(a.mk_ge(y, a.mk_int(1)), m), hi(a.mk_le(y, a.mk_int(9999)), m);
        for (expr* b : { lo.get(), hi.get() }) {
            literal l = mk_literal(b);
            if (l.sign())
                continue;
            s().set_phase(l);
            if (!m_year_pref_vars.contains(l.var()))
                m_year_pref_vars.insert(l.var());
        }
    }

    // keep the year-range preference sticky across restarts and rephasing:
    // whenever the SAT engine decides one of the preference atoms, pick the
    // in-range polarity first
    bool solver::decide(sat::bool_var& var, lbool& phase) {
        if (m_year_pref_vars.contains(var))
            phase = l_true;
        return false;
    }

    // every Date term denotes a calendar-valid date and is reconstructed
    // from its selector triple
    void solver::add_date_axioms(expr* t) {
        expr_ref y(u.mk_year(t), m), mo(u.mk_month(t), m), d(u.mk_day(t), m);
        add_year_range_preference(y);
        assert_unit(a.mk_le(a.mk_int(1), mo));
        assert_unit(a.mk_le(mo, a.mk_int(12)));
        assert_unit(a.mk_le(a.mk_int(1), d));
        assert_unit(a.mk_le(d, u.mk_days_in_month(y, mo)));
        // t = (date.mk (date.year t) (date.month t) (date.day t));
        // skipped when t already has this shape to ensure termination
        if (u.is_selector_mk(t))
            return;
        assert_unit(m.mk_eq(t, u.mk_mk(y, mo, d)));
    }

    // selector axioms for valid constructor applications
    void solver::add_mk_axioms(app* t) {
        expr* y = t->get_arg(0);
        expr* mo = t->get_arg(1);
        expr* d = t->get_arg(2);
        rational ry, rm, rd;
        if (a.is_numeral(y, ry) && a.is_numeral(mo, rm) && a.is_numeral(d, rd)) {
            if (date_util::is_valid_date(ry, rm, rd)) {
                // assert the selector equations verbatim: the rewriter would
                // evaluate the selectors to the numerals, dropping the enodes
                // needed to propagate the components to congruent date terms
                assert_unit_norewrite(m.mk_eq(u.mk_year(t), y));
                assert_unit_norewrite(m.mk_eq(u.mk_month(t), mo));
                assert_unit_norewrite(m.mk_eq(u.mk_day(t), d));
            }
            // invalid concrete constructor applications are unspecified
            return;
        }
        // symbolic date construction carries an implicit validity obligation
        // on the argument triple; with it the selector equations hold
        // unconditionally
        assert_unit(u.mk_is_valid(y, mo, d));
        assert_unit(m.mk_eq(u.mk_year(t), y));
        assert_unit(m.mk_eq(u.mk_month(t), mo));
        assert_unit(m.mk_eq(u.mk_day(t), d));
    }

    // the Rata Die number of the result of date.add/date.sub relates the
    // result triple to the argument triple and the period
    void solver::add_arith_axioms(app* t, bool is_sub) {
        expr* d = t->get_arg(0);
        expr* py = t->get_arg(1);
        expr* pm = t->get_arg(2);
        expr* pd = t->get_arg(3);
        if (is_sub) {
            py = mk_neg(py);
            pm = mk_neg(pm);
            pd = mk_neg(pd);
        }
        rational rpy, rpm, rpd;
        if (a.is_numeral(py, rpy) && a.is_numeral(pm, rpm) && a.is_numeral(pd, rpd) &&
            rpy.is_int() && rpm.is_int() && rpd.is_int() &&
            abs(rpd) <= date_util::mk_add_triple_bound()) {
            // concrete period: the result triple is a bounded case split
            // over the argument month and the day carry
            expr_ref ry(m), rmo(m), rdy(m);
            u.mk_add_triple(u.mk_year(d), u.mk_month(d), u.mk_day(d), rpy, rpm, rpd, ry, rmo, rdy);
            assert_unit(m.mk_eq(u.mk_year(t), ry));
            assert_unit(m.mk_eq(u.mk_month(t), rmo));
            assert_unit(m.mk_eq(u.mk_day(t), rdy));
            return;
        }
        expr_ref lhs = mk_rata_die(t);
        expr_ref rhs = u.mk_add_rata_die(u.mk_year(d), u.mk_month(d), u.mk_day(d), py, pm, pd);
        assert_unit(m.mk_eq(lhs, rhs));
    }

    expr_ref solver::mk_lex_cmp(expr* x, expr* y, bool strict) {
        expr_ref yx(u.mk_year(x), m), yy(u.mk_year(y), m);
        expr_ref mx(u.mk_month(x), m), my(u.mk_month(y), m);
        expr_ref dx(u.mk_day(x), m), dy(u.mk_day(y), m);
        expr* day_cmp = strict ? a.mk_lt(dx, dy) : a.mk_le(dx, dy);
        return expr_ref(
            m.mk_or(a.mk_lt(yx, yy),
                    m.mk_and(m.mk_eq(yx, yy),
                             m.mk_or(a.mk_lt(mx, my),
                                     m.mk_and(m.mk_eq(mx, my), day_cmp)))), m);
    }

    void solver::add_cmp_axioms(app* atom) {
        SASSERT(u.is_lt(atom) || u.is_le(atom) || u.is_gt(atom) || u.is_ge(atom));
        literal lit = expr2literal(atom);
        expr* x = atom->get_arg(0);
        expr* y = atom->get_arg(1);
        if (u.is_gt(atom) || u.is_ge(atom))
            std::swap(x, y);
        bool strict = u.is_lt(atom) || u.is_gt(atom);
        // lexicographic order on the selector triples ...
        assert_iff(lit, mk_lex_cmp(x, y, strict));
        // ... coincides with the order of Rata Die numbers on valid dates
        expr_ref rdx = mk_rata_die(x), rdy = mk_rata_die(y);
        assert_iff(lit, strict ? a.mk_lt(rdx, rdy) : a.mk_le(rdx, rdy));
    }

    // locate internalized selector terms for some member of the class of n
    bool solver::selector_enodes(euf::enode* n, euf::enode*& y, euf::enode*& mo, euf::enode*& d) {
        for (euf::enode* sib : euf::enode_class(n)) {
            expr* t = sib->get_expr();
            y = expr2enode(u.mk_year(t));
            mo = expr2enode(u.mk_month(t));
            d = expr2enode(u.mk_day(t));
            if (y && mo && d)
                return true;
        }
        return false;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        rational y, mo, d;
        euf::enode* ny = nullptr, * nmo = nullptr, * nd = nullptr;
        auto num_value = [&](euf::enode* sn, rational& r) {
            expr* v = values.get(sn->get_root_id(), nullptr);
            return v && a.is_numeral(v, r);
        };
        expr_ref val(m);
        if (selector_enodes(n, ny, nmo, nd) &&
            num_value(ny, y) && num_value(nmo, mo) && num_value(nd, d))
            val = u.mk_mk(a.mk_numeral(y, true), a.mk_numeral(mo, true), a.mk_numeral(d, true));
        else
            val = u.mk_mk(a.mk_int(1), a.mk_int(1), a.mk_int(1));
        values.set(n->get_root_id(), val);
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        SASSERT(u.is_date(n->get_expr()));
        euf::enode* y = nullptr, * mo = nullptr, * d = nullptr;
        if (selector_enodes(n, y, mo, d)) {
            dep.add(n, y);
            dep.add(n, mo);
            dep.add(n, d);
        }
        else
            dep.insert(n, nullptr);
        return true;
    }

    // the Rata Die numbering is injective on calendar-valid dates:
    // distinct dates have distinct day numbers
    void solver::new_diseq_eh(euf::th_eq const& eq) {
        expr* x = var2expr(eq.v1());
        expr* y = var2expr(eq.v2());
        if (!u.is_date(x) || !u.is_date(y))
            return;
        if (x->get_id() > y->get_id())
            std::swap(x, y);
        if (m_diseq_seen.contains(std::make_pair(x, y)))
            return;
        m_diseq_seen.insert(std::make_pair(x, y));
        m_diseq_trail.push_back(x);
        m_diseq_trail.push_back(y);
        expr_ref rd_eq(m.mk_eq(mk_rata_die(x), mk_rata_die(y)), m);
        m_rw(rd_eq);
        add_clause(eq_internalize(x, y), ~mk_literal(rd_eq));
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx, get_id());
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "date solver\n";
        for (unsigned v = 0; v < get_num_vars(); ++v)
            out << v << " -> " << mk_bounded_pp(var2expr(v), m) << "\n";
        return out;
    }
}
