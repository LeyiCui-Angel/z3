/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Theory solver for calendar dates and periods.
    Reduces date/period operations to integer arithmetic via eager axiom instantiation.

--*/
#include "smt/smt_context.h"
#include "smt/theory_date.h"
#include "ast/ast_pp.h"

namespace smt {

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        m_plugin(*static_cast<date_decl_plugin*>(ctx.get_manager().get_plugin(ctx.get_manager().mk_family_id("date")))),
        m_autil(ctx.get_manager()),
        m_date_year(ctx.get_manager()),
        m_date_month(ctx.get_manager()),
        m_date_day(ctx.get_manager()),
        m_axiom_trail(ctx.get_manager())
    {
    }

    theory_date::~theory_date() {}

    // -------------------------------------------------------
    // Internal date selector functions (not user-facing)
    // -------------------------------------------------------

    void theory_date::ensure_date_selectors() {
        if (m_date_year) return;
        sort* ds = m_plugin.date_sort();
        sort* is = m_autil.mk_int();
        sort* domain[1] = { ds };
        m_date_year  = m.mk_func_decl(symbol("date.year"),  1, domain, is);
        m_date_month = m.mk_func_decl(symbol("date.month"), 1, domain, is);
        m_date_day   = m.mk_func_decl(symbol("date.day"),   1, domain, is);
    }

    app_ref theory_date::mk_date_year(expr* d) {
        ensure_date_selectors();
        return app_ref(m.mk_app(m_date_year, d), m);
    }

    app_ref theory_date::mk_date_month(expr* d) {
        ensure_date_selectors();
        return app_ref(m.mk_app(m_date_month, d), m);
    }

    app_ref theory_date::mk_date_day(expr* d) {
        ensure_date_selectors();
        return app_ref(m.mk_app(m_date_day, d), m);
    }

    app_ref theory_date::mk_period_years(expr* p) {
        sort* domain[1] = { m_plugin.period_sort() };
        func_decl* fd = m.mk_func_decl(symbol("period.years"), 1, domain, m_autil.mk_int(),
                                        func_decl_info(get_family_id(), OP_PERIOD_YEARS, 0, nullptr));
        return app_ref(m.mk_app(fd, p), m);
    }

    app_ref theory_date::mk_period_months(expr* p) {
        sort* domain[1] = { m_plugin.period_sort() };
        func_decl* fd = m.mk_func_decl(symbol("period.months"), 1, domain, m_autil.mk_int(),
                                        func_decl_info(get_family_id(), OP_PERIOD_MONTHS, 0, nullptr));
        return app_ref(m.mk_app(fd, p), m);
    }

    app_ref theory_date::mk_period_days(expr* p) {
        sort* domain[1] = { m_plugin.period_sort() };
        func_decl* fd = m.mk_func_decl(symbol("period.days"), 1, domain, m_autil.mk_int(),
                                        func_decl_info(get_family_id(), OP_PERIOD_DAYS, 0, nullptr));
        return app_ref(m.mk_app(fd, p), m);
    }

    app_ref theory_date::mk_mk_date(expr* y, expr* mo, expr* d) {
        sort* is = m_autil.mk_int();
        sort* domain[3] = { is, is, is };
        func_decl* fd = m.mk_func_decl(symbol("date.mk"), 3, domain, m_plugin.date_sort(),
                                        func_decl_info(get_family_id(), OP_DATE_MK, 0, nullptr));
        expr* args[3] = { y, mo, d };
        return app_ref(m.mk_app(fd, 3, args), m);
    }

    app_ref theory_date::mk_mk_period(expr* y, expr* mo, expr* d) {
        sort* is = m_autil.mk_int();
        sort* domain[3] = { is, is, is };
        func_decl* fd = m.mk_func_decl(symbol("period.mk"), 3, domain, m_plugin.period_sort(),
                                        func_decl_info(get_family_id(), OP_PERIOD_MK, 0, nullptr));
        expr* args[3] = { y, mo, d };
        return app_ref(m.mk_app(fd, 3, args), m);
    }

    // -------------------------------------------------------
    // Axiom assertion helpers
    // -------------------------------------------------------

    void theory_date::assert_axiom(literal l) {
        ctx.mk_th_axiom(get_id(), 1, &l);
        ctx.mark_as_relevant(l);
    }

    void theory_date::assert_axiom(literal l1, literal l2) {
        literal ls[2] = { l1, l2 };
        ctx.mk_th_axiom(get_id(), 2, ls);
        ctx.mark_as_relevant(l1);
        ctx.mark_as_relevant(l2);
    }

    void theory_date::assert_eq_axiom(expr* lhs, expr* rhs) {
        ctx.internalize(lhs, false);
        ctx.internalize(rhs, false);
        literal l(mk_eq(lhs, rhs, true));
        assert_axiom(l);
    }

    void theory_date::assert_iff_axiom(expr* lhs, expr* rhs) {
        // lhs <-> rhs  ===  (lhs => rhs) /\ (rhs => lhs)
        ctx.internalize(lhs, true);
        ctx.internalize(rhs, true);
        literal l_lhs = ctx.get_literal(lhs);
        literal l_rhs = ctx.get_literal(rhs);
        // ~lhs \/ rhs
        assert_axiom(~l_lhs, l_rhs);
        // lhs \/ ~rhs
        assert_axiom(l_lhs, ~l_rhs);
    }

    bool theory_date::has_axiom(expr* e) {
        return m_axiomatized.contains(e);
    }

    void theory_date::mark_axiomatized(expr* e) {
        if (!m_axiomatized.contains(e)) {
            m_axiom_trail.push_back(e);
            m_axiomatized.insert(e);
        }
    }

    // -------------------------------------------------------
    // Theory variable management
    // -------------------------------------------------------

    theory_var theory_date::mk_var(enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        theory_var v = theory::mk_var(n);
        ctx.attach_th_var(n, this, v);
        return v;
    }

    // -------------------------------------------------------
    // Internalization
    // -------------------------------------------------------

    bool theory_date::internalize_atom(app* atom, bool gate_ctx) {
        TRACE(date, tout << "internalize_atom: " << mk_pp(atom, m) << "\n";);

        if (!m_plugin.is_date_lt(atom) && !m_plugin.is_date_le(atom) &&
            !m_plugin.is_date_gt(atom) && !m_plugin.is_date_ge(atom))
            return false;

        for (expr* arg : *atom)
            ctx.internalize(arg, false);

        if (ctx.e_internalized(atom))
            return true;

        bool_var bv = ctx.mk_bool_var(atom);
        enode* e = ctx.mk_enode(atom, false, true, true);
        decl_kind k = atom->get_decl()->get_decl_kind();
        internalize_date_cmp(atom, e, k, bv);
        return true;
    }

    bool theory_date::internalize_term(app* term) {
        TRACE(date, tout << "internalize_term: " << mk_pp(term, m) << "\n";);

        for (expr* arg : *term)
            ctx.internalize(arg, false);

        if (ctx.e_internalized(term))
            return true;

        enode* e = ctx.mk_enode(term, false, m.is_bool(term), true);

        if (!m_plugin.is_date(term) && !m_plugin.is_period(term))
            return true;

        mk_var(e);

        decl_kind k = term->get_decl()->get_decl_kind();
        switch (k) {
        case OP_DATE_MK:
            internalize_mk_date(term, e);
            break;
        case OP_PERIOD_MK:
            internalize_mk_period(term, e);
            break;
        case OP_PERIOD_YEARS:
        case OP_PERIOD_MONTHS:
        case OP_PERIOD_DAYS:
            internalize_period_selector(term, e);
            break;
        case OP_DATE_ADD:
            internalize_date_add(term, e);
            break;
        case OP_DATE_SUB:
            internalize_date_sub(term, e);
            break;
        case OP_PERIOD_ADD:
            internalize_period_add(term, e);
            break;
        case OP_PERIOD_SUB:
            internalize_period_sub(term, e);
            break;
        case OP_PERIOD_MUL:
            internalize_period_mul(term, e);
            break;
        default:
            break;
        }
        return true;
    }

    void theory_date::apply_sort_cnstr(enode* n, sort* s) {
        if (m_plugin.is_date(s) || m_plugin.is_period(s)) {
            mk_var(n);
        }
    }

    // -------------------------------------------------------
    // Axiom generation for specific term kinds
    // -------------------------------------------------------

    void theory_date::internalize_mk_date(app* term, enode* e) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        assert_date_accessor_axioms(e);
    }

    void theory_date::internalize_mk_period(app* term, enode* e) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        assert_period_accessor_axioms(e);
    }

    void theory_date::internalize_period_selector(app* term, enode* e) {
        // Axioms will be generated when the constructor is seen
        // (via assert_period_accessor_axioms)
    }

    // date_add(d, p) = mk-date(date-year(d) + p-years(p), date-month(d) + p-months(p), date-day(d) + p-days(p))
    void theory_date::internalize_date_add(app* term, enode* e) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        expr* d = term->get_arg(0);
        expr* p = term->get_arg(1);
        app_ref rhs = mk_mk_date(
            m_autil.mk_add(mk_date_year(d),  mk_period_years(p)),
            m_autil.mk_add(mk_date_month(d), mk_period_months(p)),
            m_autil.mk_add(mk_date_day(d),   mk_period_days(p)));
        assert_eq_axiom(term, rhs);
    }

    // date_sub(d, p) = mk-date(date-year(d) - p-years(p), date-month(d) - p-months(p), date-day(d) - p-days(p))
    void theory_date::internalize_date_sub(app* term, enode* e) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        expr* d = term->get_arg(0);
        expr* p = term->get_arg(1);
        app_ref rhs = mk_mk_date(
            m_autil.mk_sub(mk_date_year(d),  mk_period_years(p)),
            m_autil.mk_sub(mk_date_month(d), mk_period_months(p)),
            m_autil.mk_sub(mk_date_day(d),   mk_period_days(p)));
        assert_eq_axiom(term, rhs);
    }

    // period_add(p1, p2) = mk-period(p-years(p1)+p-years(p2), ...)
    void theory_date::internalize_period_add(app* term, enode* e) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        expr* p1 = term->get_arg(0);
        expr* p2 = term->get_arg(1);
        app_ref rhs = mk_mk_period(
            m_autil.mk_add(mk_period_years(p1),  mk_period_years(p2)),
            m_autil.mk_add(mk_period_months(p1), mk_period_months(p2)),
            m_autil.mk_add(mk_period_days(p1),   mk_period_days(p2)));
        assert_eq_axiom(term, rhs);
    }

    // period_sub(p1, p2) = mk-period(p-years(p1)-p-years(p2), ...)
    void theory_date::internalize_period_sub(app* term, enode* e) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        expr* p1 = term->get_arg(0);
        expr* p2 = term->get_arg(1);
        app_ref rhs = mk_mk_period(
            m_autil.mk_sub(mk_period_years(p1),  mk_period_years(p2)),
            m_autil.mk_sub(mk_period_months(p1), mk_period_months(p2)),
            m_autil.mk_sub(mk_period_days(p1),   mk_period_days(p2)));
        assert_eq_axiom(term, rhs);
    }

    // period_mul(p, k) = mk-period(p-years(p)*k, p-months(p)*k, p-days(p)*k)
    void theory_date::internalize_period_mul(app* term, enode* e) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        expr* p = term->get_arg(0);
        expr* k = term->get_arg(1);
        app_ref rhs = mk_mk_period(
            m_autil.mk_mul(mk_period_years(p),  k),
            m_autil.mk_mul(mk_period_months(p), k),
            m_autil.mk_mul(mk_period_days(p),   k));
        assert_eq_axiom(term, rhs);
    }

    // date_lt/le/gt/ge(d1, d2) <-> lexicographic comparison on (year, month, day)
    void theory_date::internalize_date_cmp(app* term, enode* e, decl_kind k, bool_var bv) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);

        expr* d1 = term->get_arg(0);
        expr* d2 = term->get_arg(1);

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

        // Build lexicographic comparison using only OP_LE (not OP_LT/OP_GT
        // which the arithmetic solver's internalize_atom doesn't handle).
        // a < b  =  not(b <= a)
        // a <= b  =  (a <= b)
        // cmp = ly \/ (ey /\ (lm \/ (em /\ ld)))
        expr_ref ly(m), lm(m), ld(m);
        expr_ref ey(m.mk_eq(y1, y2), m);
        expr_ref em(m.mk_eq(mo1, mo2), m);

        switch (k) {
        case OP_DATE_LT:
            ly = m.mk_not(m_autil.mk_le(y2, y1));       // y1 < y2
            lm = m.mk_not(m_autil.mk_le(mo2, mo1));     // mo1 < mo2
            ld = m.mk_not(m_autil.mk_le(dy2, dy1));     // dy1 < dy2
            break;
        case OP_DATE_LE:
            ly = m.mk_not(m_autil.mk_le(y2, y1));       // y1 < y2
            lm = m.mk_not(m_autil.mk_le(mo2, mo1));     // mo1 < mo2
            ld = m_autil.mk_le(dy1, dy2);               // dy1 <= dy2
            break;
        case OP_DATE_GT:
            ly = m.mk_not(m_autil.mk_le(y1, y2));       // y2 < y1
            lm = m.mk_not(m_autil.mk_le(mo1, mo2));     // mo2 < mo1
            ld = m.mk_not(m_autil.mk_le(dy1, dy2));     // dy2 < dy1
            break;
        case OP_DATE_GE:
            ly = m.mk_not(m_autil.mk_le(y1, y2));       // y2 < y1
            lm = m.mk_not(m_autil.mk_le(mo1, mo2));     // mo2 < mo1
            ld = m_autil.mk_le(dy2, dy1);               // dy2 <= dy1
            break;
        default:
            UNREACHABLE();
        }

        expr_ref cmp(m.mk_or(ly, m.mk_and(ey, m.mk_or(lm, m.mk_and(em, ld)))), m);

        // Internalize the comparison expression and assert iff with the atom.
        // We must NOT re-internalize term (we're inside internalize_atom for it).
        ctx.internalize(cmp, true);
        literal l_atom(bv);
        literal l_cmp = ctx.get_literal(cmp);
        assert_axiom(~l_atom, l_cmp);
        assert_axiom(l_atom, ~l_cmp);
    }

    // For mk-date(y, m, d): assert date-year(mk-date(y,m,d)) = y, etc.
    void theory_date::assert_date_accessor_axioms(enode* n) {
        app* term = n->get_expr();
        SASSERT(m_plugin.is_mk_date(term));
        expr* y  = term->get_arg(0);
        expr* mo = term->get_arg(1);
        expr* d  = term->get_arg(2);
        assert_eq_axiom(mk_date_year(term),  y);
        assert_eq_axiom(mk_date_month(term), mo);
        assert_eq_axiom(mk_date_day(term),   d);
    }

    // For mk-period(y, m, d): assert p-years(mk-period(y,m,d)) = y, etc.
    void theory_date::assert_period_accessor_axioms(enode* n) {
        app* term = n->get_expr();
        SASSERT(m_plugin.is_mk_period(term));
        expr* y  = term->get_arg(0);
        expr* mo = term->get_arg(1);
        expr* d  = term->get_arg(2);
        assert_eq_axiom(mk_period_years(term),  y);
        assert_eq_axiom(mk_period_months(term), mo);
        assert_eq_axiom(mk_period_days(term),   d);
    }

    // Reconstruction: d = mk-date(date-year(d), date-month(d), date-day(d))
    void theory_date::assert_date_reconstruction(enode* n) {
        expr* e = n->get_expr();
        if (has_axiom(e)) return;
        mark_axiomatized(e);
        app_ref rhs = mk_mk_date(mk_date_year(e), mk_date_month(e), mk_date_day(e));
        assert_eq_axiom(e, rhs);
    }

    // Reconstruction: p = mk-period(p-years(p), p-months(p), p-days(p))
    void theory_date::assert_period_reconstruction(enode* n) {
        expr* e = n->get_expr();
        if (has_axiom(e)) return;
        mark_axiomatized(e);
        app_ref rhs = mk_mk_period(mk_period_years(e), mk_period_months(e), mk_period_days(e));
        assert_eq_axiom(e, rhs);
    }

    // -------------------------------------------------------
    // Equality / Disequality
    // -------------------------------------------------------

    void theory_date::new_eq_eh(theory_var v1, theory_var v2) {
        // When two constructor terms are equated, injectivity applies.
        // The axiom system already handles this: if mk-date(y1,m1,d1) = mk-date(y2,m2,d2)
        // then via accessor axioms: y1 = date-year(mk-date(y1,m1,d1)) = date-year(mk-date(y2,m2,d2)) = y2
        // So injectivity is automatically derived.
    }

    // -------------------------------------------------------
    // Final check — ensure all Date/Period terms have reconstruction axioms
    // -------------------------------------------------------

    final_check_status theory_date::final_check_eh(unsigned) {
        bool added = false;
        unsigned n = get_num_vars();
        for (unsigned i = 0; i < n; ++i) {
            enode* e = get_enode(i);
            if (!e) continue;
            expr* ex = e->get_expr();
            sort* s = ex->get_sort();
            if (m_plugin.is_date(s) && !has_axiom(ex)) {
                assert_date_reconstruction(e);
                added = true;
            }
            if (m_plugin.is_period(s) && !has_axiom(ex)) {
                assert_period_reconstruction(e);
                added = true;
            }
        }
        return added ? FC_CONTINUE : FC_DONE;
    }

    // -------------------------------------------------------
    // Backtracking
    // -------------------------------------------------------

    void theory_date::push_scope_eh() {
        theory::push_scope_eh();
    }

    void theory_date::pop_scope_eh(unsigned num_scopes) {
        theory::pop_scope_eh(num_scopes);
    }

    void theory_date::reset_eh() {
        m_axiomatized.reset();
        m_axiom_trail.reset();
        theory::reset_eh();
    }

    // -------------------------------------------------------
    // Display
    // -------------------------------------------------------

    void theory_date::display(std::ostream& out) const {
        out << "theory_date: " << get_num_vars() << " vars\n";
    }
}
