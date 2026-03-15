/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates and periods (new SAT/SMT core).
    Reduces date/period operations to integer arithmetic via eager axiom instantiation.

--*/
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"
#include "ast/ast_pp.h"

namespace date {

    solver::solver(euf::solver& ctx, theory_id id) :
        th_euf_solver(ctx, ctx.get_manager().get_family_name(id), id),
        m_plugin(*static_cast<date_decl_plugin*>(m.get_plugin(id))),
        m_autil(m),
        m_date_year(m),
        m_date_month(m),
        m_date_day(m)
    {}

    // -------------------------------------------------------
    // Internal date selector functions (not user-facing)
    // -------------------------------------------------------

    void solver::ensure_date_selectors() {
        if (m_date_year) return;
        sort* ds = m_plugin.date_sort();
        sort* is = m_autil.mk_int();
        sort* domain[1] = { ds };
        m_date_year  = m.mk_func_decl(symbol("date.year"),  1, domain, is);
        m_date_month = m.mk_func_decl(symbol("date.month"), 1, domain, is);
        m_date_day   = m.mk_func_decl(symbol("date.day"),   1, domain, is);
    }

    app_ref solver::mk_date_year(expr* d) {
        ensure_date_selectors();
        return app_ref(m.mk_app(m_date_year, d), m);
    }

    app_ref solver::mk_date_month(expr* d) {
        ensure_date_selectors();
        return app_ref(m.mk_app(m_date_month, d), m);
    }

    app_ref solver::mk_date_day(expr* d) {
        ensure_date_selectors();
        return app_ref(m.mk_app(m_date_day, d), m);
    }

    app_ref solver::mk_period_years(expr* p) {
        sort* domain[1] = { m_plugin.period_sort() };
        func_decl* fd = m.mk_func_decl(symbol("period.years"), 1, domain, m_autil.mk_int(),
                                        func_decl_info(get_id(), OP_PERIOD_YEARS, 0, nullptr));
        return app_ref(m.mk_app(fd, p), m);
    }

    app_ref solver::mk_period_months(expr* p) {
        sort* domain[1] = { m_plugin.period_sort() };
        func_decl* fd = m.mk_func_decl(symbol("period.months"), 1, domain, m_autil.mk_int(),
                                        func_decl_info(get_id(), OP_PERIOD_MONTHS, 0, nullptr));
        return app_ref(m.mk_app(fd, p), m);
    }

    app_ref solver::mk_period_days(expr* p) {
        sort* domain[1] = { m_plugin.period_sort() };
        func_decl* fd = m.mk_func_decl(symbol("period.days"), 1, domain, m_autil.mk_int(),
                                        func_decl_info(get_id(), OP_PERIOD_DAYS, 0, nullptr));
        return app_ref(m.mk_app(fd, p), m);
    }

    app_ref solver::mk_mk_date(expr* y, expr* mo, expr* d) {
        sort* is = m_autil.mk_int();
        sort* domain[3] = { is, is, is };
        func_decl* fd = m.mk_func_decl(symbol("date.mk"), 3, domain, m_plugin.date_sort(),
                                        func_decl_info(get_id(), OP_DATE_MK, 0, nullptr));
        expr* args[3] = { y, mo, d };
        return app_ref(m.mk_app(fd, 3, args), m);
    }

    app_ref solver::mk_mk_period(expr* y, expr* mo, expr* d) {
        sort* is = m_autil.mk_int();
        sort* domain[3] = { is, is, is };
        func_decl* fd = m.mk_func_decl(symbol("period.mk"), 3, domain, m_plugin.period_sort(),
                                        func_decl_info(get_id(), OP_PERIOD_MK, 0, nullptr));
        expr* args[3] = { y, mo, d };
        return app_ref(m.mk_app(fd, 3, args), m);
    }

    // -------------------------------------------------------
    // Axiom helpers
    // -------------------------------------------------------

    void solver::assert_eq_axiom(expr* lhs, expr* rhs) {
        sat::literal l = eq_internalize(lhs, rhs);
        add_unit(l);
    }

    void solver::assert_iff_axiom(expr* lhs, expr* rhs) {
        sat::literal l_lhs = mk_literal(lhs);
        sat::literal l_rhs = mk_literal(rhs);
        add_clause(~l_lhs, l_rhs);
        add_clause(l_lhs, ~l_rhs);
    }

    // -------------------------------------------------------
    // Axiom generation
    // -------------------------------------------------------

    void solver::axiomatize_mk_date(expr* term) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        app* a = to_app(term);
        expr* y  = a->get_arg(0);
        expr* mo = a->get_arg(1);
        expr* d  = a->get_arg(2);
        assert_eq_axiom(mk_date_year(term),  y);
        assert_eq_axiom(mk_date_month(term), mo);
        assert_eq_axiom(mk_date_day(term),   d);
    }

    void solver::axiomatize_mk_period(expr* term) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        app* a = to_app(term);
        expr* y  = a->get_arg(0);
        expr* mo = a->get_arg(1);
        expr* d  = a->get_arg(2);
        assert_eq_axiom(mk_period_years(term),  y);
        assert_eq_axiom(mk_period_months(term), mo);
        assert_eq_axiom(mk_period_days(term),   d);
    }

    void solver::axiomatize_date_add(expr* term) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        app* a = to_app(term);
        expr* d = a->get_arg(0);
        expr* p = a->get_arg(1);
        app_ref rhs = mk_mk_date(
            m_autil.mk_add(mk_date_year(d),  mk_period_years(p)),
            m_autil.mk_add(mk_date_month(d), mk_period_months(p)),
            m_autil.mk_add(mk_date_day(d),   mk_period_days(p)));
        assert_eq_axiom(term, rhs);
    }

    void solver::axiomatize_date_sub(expr* term) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        app* a = to_app(term);
        expr* d = a->get_arg(0);
        expr* p = a->get_arg(1);
        app_ref rhs = mk_mk_date(
            m_autil.mk_sub(mk_date_year(d),  mk_period_years(p)),
            m_autil.mk_sub(mk_date_month(d), mk_period_months(p)),
            m_autil.mk_sub(mk_date_day(d),   mk_period_days(p)));
        assert_eq_axiom(term, rhs);
    }

    void solver::axiomatize_period_add(expr* term) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        app* a = to_app(term);
        expr* p1 = a->get_arg(0);
        expr* p2 = a->get_arg(1);
        app_ref rhs = mk_mk_period(
            m_autil.mk_add(mk_period_years(p1),  mk_period_years(p2)),
            m_autil.mk_add(mk_period_months(p1), mk_period_months(p2)),
            m_autil.mk_add(mk_period_days(p1),   mk_period_days(p2)));
        assert_eq_axiom(term, rhs);
    }

    void solver::axiomatize_period_sub(expr* term) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        app* a = to_app(term);
        expr* p1 = a->get_arg(0);
        expr* p2 = a->get_arg(1);
        app_ref rhs = mk_mk_period(
            m_autil.mk_sub(mk_period_years(p1),  mk_period_years(p2)),
            m_autil.mk_sub(mk_period_months(p1), mk_period_months(p2)),
            m_autil.mk_sub(mk_period_days(p1),   mk_period_days(p2)));
        assert_eq_axiom(term, rhs);
    }

    void solver::axiomatize_period_mul(expr* term) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        app* a = to_app(term);
        expr* p = a->get_arg(0);
        expr* k = a->get_arg(1);
        app_ref rhs = mk_mk_period(
            m_autil.mk_mul(mk_period_years(p),  k),
            m_autil.mk_mul(mk_period_months(p), k),
            m_autil.mk_mul(mk_period_days(p),   k));
        assert_eq_axiom(term, rhs);
    }

    void solver::axiomatize_date_cmp(expr* term, decl_kind k) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        app* a = to_app(term);
        expr* d1 = a->get_arg(0);
        expr* d2 = a->get_arg(1);

        // Get components — use constructor args directly when available
        expr_ref y1(m), mo1(m), dy1(m), y2(m), mo2(m), dy2(m);
        if (m_plugin.is_mk_date(d1)) {
            y1 = to_app(d1)->get_arg(0); mo1 = to_app(d1)->get_arg(1); dy1 = to_app(d1)->get_arg(2);
        } else {
            y1 = mk_date_year(d1); mo1 = mk_date_month(d1); dy1 = mk_date_day(d1);
        }
        if (m_plugin.is_mk_date(d2)) {
            y2 = to_app(d2)->get_arg(0); mo2 = to_app(d2)->get_arg(1); dy2 = to_app(d2)->get_arg(2);
        } else {
            y2 = mk_date_year(d2); mo2 = mk_date_month(d2); dy2 = mk_date_day(d2);
        }

        // Build lexicographic comparison using only OP_LE (not OP_LT/OP_GT).
        // a < b  =  not(b <= a)
        // cmp = ly \/ (ey /\ (lm \/ (em /\ ld)))
        expr_ref ly(m), lm(m), ld(m);
        expr_ref ey(m.mk_eq(y1, y2), m);
        expr_ref em(m.mk_eq(mo1, mo2), m);

        switch (k) {
        case OP_DATE_LT:
            ly = m.mk_not(m_autil.mk_le(y2, y1));
            lm = m.mk_not(m_autil.mk_le(mo2, mo1));
            ld = m.mk_not(m_autil.mk_le(dy2, dy1));
            break;
        case OP_DATE_LE:
            ly = m.mk_not(m_autil.mk_le(y2, y1));
            lm = m.mk_not(m_autil.mk_le(mo2, mo1));
            ld = m_autil.mk_le(dy1, dy2);
            break;
        case OP_DATE_GT:
            ly = m.mk_not(m_autil.mk_le(y1, y2));
            lm = m.mk_not(m_autil.mk_le(mo1, mo2));
            ld = m.mk_not(m_autil.mk_le(dy1, dy2));
            break;
        case OP_DATE_GE:
            ly = m.mk_not(m_autil.mk_le(y1, y2));
            lm = m.mk_not(m_autil.mk_le(mo1, mo2));
            ld = m_autil.mk_le(dy2, dy1);
            break;
        default:
            UNREACHABLE();
        }

        expr_ref cmp(m.mk_or(ly, m.mk_and(ey, m.mk_or(lm, m.mk_and(em, ld)))), m);
        assert_iff_axiom(term, cmp);
    }

    void solver::axiomatize_date_reconstruction(expr* e) {
        if (has_axiom(e)) return;
        mark_axiomatized(e);
        app_ref rhs = mk_mk_date(mk_date_year(e), mk_date_month(e), mk_date_day(e));
        assert_eq_axiom(e, rhs);
    }

    void solver::axiomatize_period_reconstruction(expr* e) {
        if (has_axiom(e)) return;
        mark_axiomatized(e);
        app_ref rhs = mk_mk_period(mk_period_years(e), mk_period_months(e), mk_period_days(e));
        assert_eq_axiom(e, rhs);
    }

    // -------------------------------------------------------
    // Internalization
    // -------------------------------------------------------

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
            sort* s = e->get_sort();
            if (m_plugin.is_date(s) || m_plugin.is_period(s))
                mk_var(expr2enode(e));
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());
    }

    bool solver::post_visit(expr* term, bool sign, bool root) {
        euf::enode* n = expr2enode(term);
        if (!n)
            n = mk_enode(term);
        if (!n->is_attached_to(get_id()))
            mk_var(n);

        app* a = to_app(term);
        decl_kind k = a->get_decl()->get_decl_kind();

        switch (k) {
        case OP_DATE_MK:     axiomatize_mk_date(term); break;
        case OP_PERIOD_MK:   axiomatize_mk_period(term); break;
        case OP_DATE_ADD:    axiomatize_date_add(term); break;
        case OP_DATE_SUB:    axiomatize_date_sub(term); break;
        case OP_PERIOD_ADD:  axiomatize_period_add(term); break;
        case OP_PERIOD_SUB:  axiomatize_period_sub(term); break;
        case OP_PERIOD_MUL:  axiomatize_period_mul(term); break;
        case OP_DATE_LT:
        case OP_DATE_LE:
        case OP_DATE_GT:
        case OP_DATE_GE:     axiomatize_date_cmp(term, k); break;
        default: break;
        }

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
        if (m_plugin.is_date(s) || m_plugin.is_period(s))
            mk_var(n);
    }

    // -------------------------------------------------------
    // Final check — constructor completion
    // -------------------------------------------------------

    sat::check_result solver::check() {
        bool added = false;
        unsigned n = get_num_vars();
        for (unsigned i = 0; i < n; ++i) {
            euf::enode* e = var2enode(i);
            if (!e) continue;
            expr* ex = e->get_expr();
            sort* s = ex->get_sort();
            if (m_plugin.is_date(s) && !has_axiom(ex)) {
                axiomatize_date_reconstruction(ex);
                added = true;
            }
            if (m_plugin.is_period(s) && !has_axiom(ex)) {
                axiomatize_period_reconstruction(ex);
                added = true;
            }
        }
        return added ? sat::check_result::CR_CONTINUE : sat::check_result::CR_DONE;
    }

    // -------------------------------------------------------
    // Backtracking / state
    // -------------------------------------------------------

    void solver::pop_core(unsigned n) {
        th_euf_solver::pop_core(n);
    }

    void solver::get_antecedents(sat::literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) {
        auto& jst = euf::th_explain::from_index(idx);
        for (auto lit : euf::th_explain::lits(jst))
            r.push_back(lit);
    }

    // -------------------------------------------------------
    // Model building
    // -------------------------------------------------------

    // Walk the equivalence class of n to find a mk-date or mk-period constructor.
    euf::enode* solver::find_constructor(euf::enode* n) {
        sort* s = n->get_expr()->get_sort();
        bool want_date = m_plugin.is_date(s);
        bool want_period = m_plugin.is_period(s);
        if (!want_date && !want_period)
            return nullptr;
        euf::enode* root = n->get_root();
        euf::enode* curr = root;
        do {
            expr* ce = curr->get_expr();
            if (want_date && m_plugin.is_mk_date(ce))
                return curr;
            if (want_period && m_plugin.is_mk_period(ce))
                return curr;
            curr = curr->get_next();
        } while (curr != root);
        return nullptr;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        expr* e = n->get_expr();
        sort* s = e->get_sort();
        if (!m_plugin.is_date(s) && !m_plugin.is_period(s))
            return;

        // Find a constructor (mk-date / mk-period) in the equivalence class.
        euf::enode* con = find_constructor(n);
        if (con && con->num_args() == 3) {
            expr* y_val = values.get(con->get_arg(0)->get_root_id(), nullptr);
            expr* m_val = values.get(con->get_arg(1)->get_root_id(), nullptr);
            expr* d_val = values.get(con->get_arg(2)->get_root_id(), nullptr);
            if (y_val && m_val && d_val) {
                if (m_plugin.is_date(s))
                    values.setx(n->get_root_id(), mk_mk_date(y_val, m_val, d_val));
                else
                    values.setx(n->get_root_id(), mk_mk_period(y_val, m_val, d_val));
                return;
            }
        }

        // Fallback to default value.
        if (m_plugin.is_date(s))
            values.setx(n->get_root_id(), m_plugin.mk_default_date(m));
        else
            values.setx(n->get_root_id(), m_plugin.mk_default_period(m));
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        expr* e = n->get_expr();
        sort* s = e->get_sort();
        if (!m_plugin.is_date(s) && !m_plugin.is_period(s))
            return false;

        // Find a constructor in the equivalence class and depend on its args.
        euf::enode* con = find_constructor(n);
        if (con && con->num_args() == 3) {
            for (euf::enode* arg : euf::enode_args(con))
                dep.add(n, arg->get_root());
            return true;
        }

        dep.insert(n, nullptr);
        return true;
    }

    bool solver::include_func_interp(func_decl* f) const {
        // Period selectors (p-years, p-months, p-days) are in our family.
        // Include their interpretation so the model evaluator can handle them.
        if (f->get_family_id() == get_id()) {
            switch (f->get_decl_kind()) {
            case OP_PERIOD_YEARS:
            case OP_PERIOD_MONTHS:
            case OP_PERIOD_DAYS:
                return true;
            default:
                break;
            }
        }
        return false;
    }

    // -------------------------------------------------------
    // Clone / display
    // -------------------------------------------------------

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx, get_id());
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out << "date-solver: " << get_num_vars() << " vars\n";
    }
}
