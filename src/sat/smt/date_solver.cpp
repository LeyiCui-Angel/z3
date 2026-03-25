/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates and periods (new SAT/SMT core).
    Reduces date/period operations to integer arithmetic via eager axiom instantiation.

    Date semantics follow the DateSAT framework:
    - Valid dates: any year, month 1-12, day 1-dim(y,m)
    - date.add: month normalization + EOM clamp + epoch-based day carry
    - Comparisons: lexicographic on (year, month, day) for valid dates

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
    {
    }

    // -------------------------------------------------------
    // Internal date selector functions (not user-facing)
    // -------------------------------------------------------

    void solver::ensure_date_selectors() {
        if (m_date_year) return;
        sort* ds = m_plugin.date_sort();
        sort* is = m_autil.mk_int();
        sort* domain[1] = { ds };
        m_date_year  = m.mk_func_decl(symbol("date.year"),  1, domain, is,
                                        func_decl_info(get_id(), OP_DATE_YEAR, 0, nullptr));
        m_date_month = m.mk_func_decl(symbol("date.month"), 1, domain, is,
                                        func_decl_info(get_id(), OP_DATE_MONTH, 0, nullptr));
        m_date_day   = m.mk_func_decl(symbol("date.day"),   1, domain, is,
                                        func_decl_info(get_id(), OP_DATE_DAY, 0, nullptr));
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
    // Calendar arithmetic expression builders
    // -------------------------------------------------------

    expr_ref solver::mk_is_leap(expr* y) {
        // (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
        expr_ref zero(m_autil.mk_int(0), m);
        expr_ref y4(m_autil.mk_mod(y, m_autil.mk_int(4)), m);
        expr_ref y100(m_autil.mk_mod(y, m_autil.mk_int(100)), m);
        expr_ref y400(m_autil.mk_mod(y, m_autil.mk_int(400)), m);
        expr_ref eq4(m.mk_eq(y4, zero), m);
        expr_ref neq100(m.mk_not(m.mk_eq(y100, zero)), m);
        expr_ref eq400(m.mk_eq(y400, zero), m);
        return expr_ref(m.mk_or(m.mk_and(eq4, neq100), eq400), m);
    }

    expr_ref solver::mk_days_in_month(expr* y, expr* mo) {
        // m==2 → (leap?29:28), m∈{4,6,9,11}→30, else→31
        expr_ref leap_br(m.mk_ite(mk_is_leap(y), m_autil.mk_int(29), m_autil.mk_int(28)), m);
        expr_ref is_30(m.mk_or(
            m.mk_or(m.mk_eq(mo, m_autil.mk_int(4)), m.mk_eq(mo, m_autil.mk_int(6))),
            m.mk_or(m.mk_eq(mo, m_autil.mk_int(9)), m.mk_eq(mo, m_autil.mk_int(11)))), m);
        return expr_ref(m.mk_ite(m.mk_eq(mo, m_autil.mk_int(2)), leap_br,
                                 m.mk_ite(is_30, m_autil.mk_int(30), m_autil.mk_int(31))), m);
    }

    void solver::mk_normalize_month(expr* base_y, expr* raw_m,
                                     expr_ref& out_y, expr_ref& out_m) {
        // raw_m is 1-based month (may be outside [1,12])
        // t = raw_m - 1 (0-based)
        // out_y = base_y + t div 12
        // out_m = t mod 12 + 1
        // Z3 Euclidean div/mod with positive divisor: mod always >= 0
        expr_ref t(m_autil.mk_sub(raw_m, m_autil.mk_int(1)), m);
        expr_ref q(m_autil.mk_idiv(t, m_autil.mk_int(12)), m);
        expr_ref r(m_autil.mk_mod(t, m_autil.mk_int(12)), m);
        out_y = expr_ref(m_autil.mk_add(base_y, q), m);
        out_m = expr_ref(m_autil.mk_add(r, m_autil.mk_int(1)), m);
    }

    expr_ref solver::mk_eom_clamp(expr* y, expr* mo, expr* d) {
        // min(d, days_in_month(y, m))
        expr_ref dim = mk_days_in_month(y, mo);
        // ITE(not(d <= dim), dim, d)  i.e. ITE(d > dim, dim, d)
        return expr_ref(m.mk_ite(m.mk_not(m_autil.mk_le(d, dim)), dim, d), m);
    }

    expr_ref solver::mk_ymd_to_epoch(expr* y, expr* mo, expr* d) {
        // Civil (y,m,d) → epoch days since 2000-03-01
        // Howard Hinnant's chrono-compatible algorithm
        expr_ref two(m_autil.mk_int(2), m);
        expr_ref m_le_2(m_autil.mk_le(mo, two), m);

        // Shift Jan/Feb into previous March-based year
        expr_ref y_adj(m.mk_ite(m_le_2, m_autil.mk_sub(y, m_autil.mk_int(1)), y), m);
        expr_ref m_adj(m.mk_ite(m_le_2, m_autil.mk_add(mo, m_autil.mk_int(12)), mo), m);
        expr_ref mp(m_autil.mk_sub(m_adj, m_autil.mk_int(3)), m); // 0..11

        // Era decomposition
        expr_ref i400(m_autil.mk_int(400), m);
        expr_ref era(m_autil.mk_idiv(y_adj, i400), m);
        expr_ref yoe(m_autil.mk_sub(y_adj, m_autil.mk_mul(era, i400)), m); // 0..399

        // Day of year within March-based year
        expr_ref doy(m_autil.mk_add(
            m_autil.mk_idiv(
                m_autil.mk_add(m_autil.mk_mul(m_autil.mk_int(153), mp), m_autil.mk_int(2)),
                m_autil.mk_int(5)),
            m_autil.mk_sub(d, m_autil.mk_int(1))), m);

        // Day of era: yoe*365 + yoe/4 - yoe/100 + doy
        expr_ref doe(m_autil.mk_add(
            m_autil.mk_sub(
                m_autil.mk_add(m_autil.mk_mul(yoe, m_autil.mk_int(365)),
                               m_autil.mk_idiv(yoe, m_autil.mk_int(4))),
                m_autil.mk_idiv(yoe, m_autil.mk_int(100))),
            doy), m);

        // Absolute days → epoch days
        expr_ref abs_days(m_autil.mk_add(m_autil.mk_mul(era, m_autil.mk_int(146097)), doe), m);
        return expr_ref(m_autil.mk_sub(abs_days, m_autil.mk_int(730485)), m);
    }

    void solver::mk_epoch_to_ymd(expr* epoch, expr_ref& out_y, expr_ref& out_m, expr_ref& out_d) {
        // Epoch days since 2000-03-01 → civil (y,m,d)
        // Howard Hinnant's chrono-compatible algorithm

        // Convert to absolute days since 0000-03-01
        expr_ref z(m_autil.mk_add(epoch, m_autil.mk_int(730485)), m);
        expr_ref three(m_autil.mk_int(3), m);

        // 400-year cycles (era)
        expr_ref era(m_autil.mk_idiv(z, m_autil.mk_int(146097)), m);
        expr_ref doe(m_autil.mk_sub(z, m_autil.mk_mul(era, m_autil.mk_int(146097))), m);

        // 100-year blocks (clamp: max 3)
        expr_ref q100_raw(m_autil.mk_idiv(doe, m_autil.mk_int(36524)), m);
        expr_ref q100(m.mk_ite(
            m.mk_not(m_autil.mk_le(q100_raw, three)),
            three, q100_raw), m);
        expr_ref r100(m_autil.mk_sub(doe, m_autil.mk_mul(q100, m_autil.mk_int(36524))), m);

        // 4-year blocks
        expr_ref q4(m_autil.mk_idiv(r100, m_autil.mk_int(1461)), m);
        expr_ref r4(m_autil.mk_mod(r100, m_autil.mk_int(1461)), m);

        // 1-year blocks (clamp: max 3)
        expr_ref q1_raw(m_autil.mk_idiv(r4, m_autil.mk_int(365)), m);
        expr_ref q1(m.mk_ite(
            m.mk_not(m_autil.mk_le(q1_raw, three)),
            three, q1_raw), m);
        expr_ref r1(m_autil.mk_sub(r4, m_autil.mk_mul(q1, m_autil.mk_int(365))), m);

        // March-based year = era*400 + yoe (no +2000 offset, z is absolute)
        expr_ref yoe(m_autil.mk_add(
            m_autil.mk_mul(q100, m_autil.mk_int(100)),
            m_autil.mk_add(m_autil.mk_mul(q4, m_autil.mk_int(4)), q1)), m);
        expr_ref y(m_autil.mk_add(m_autil.mk_mul(era, m_autil.mk_int(400)), yoe), m);

        // Month from day-of-year: mp = (5*r1 + 2) / 153
        expr_ref mp(m_autil.mk_idiv(
            m_autil.mk_add(m_autil.mk_mul(m_autil.mk_int(5), r1), m_autil.mk_int(2)),
            m_autil.mk_int(153)), m);

        // Day of month
        out_d = expr_ref(m_autil.mk_add(
            m_autil.mk_sub(r1,
                m_autil.mk_idiv(
                    m_autil.mk_add(m_autil.mk_mul(m_autil.mk_int(153), mp), m_autil.mk_int(2)),
                    m_autil.mk_int(5))),
            m_autil.mk_int(1)), m);

        // Calendar month: mp+3, wrap Jan(13)/Feb(14) → 1/2
        expr_ref m_raw(m_autil.mk_add(mp, m_autil.mk_int(3)), m);
        out_m = expr_ref(m.mk_ite(
            m.mk_not(m_autil.mk_le(m_raw, m_autil.mk_int(12))),
            m_autil.mk_sub(m_raw, m_autil.mk_int(12)),
            m_raw), m);

        // Gregorian year: Jan/Feb belong to next year
        out_y = expr_ref(m.mk_ite(
            m_autil.mk_le(out_m, m_autil.mk_int(2)),
            m_autil.mk_add(y, m_autil.mk_int(1)),
            y), m);
    }

    // -------------------------------------------------------
    // Concrete C++ calendar arithmetic
    // -------------------------------------------------------

    bool solver::cc_is_leap(int y) {
        return (y % 4 == 0 && y % 100 != 0) || y % 400 == 0;
    }

    int solver::cc_days_in_month(int y, int m) {
        static const int days[] = {0,31,28,31,30,31,30,31,31,30,31,30,31};
        if (m < 1 || m > 12) return 30;
        if (m == 2 && cc_is_leap(y)) return 29;
        return days[m];
    }

    int solver::cc_ymd_to_epoch(int y, int m, int d) {
        // Civil (y,m,d) -> epoch days since 2000-03-01 (Hinnant algorithm)
        int y_adj = (m <= 2) ? y - 1 : y;
        int m_adj = (m <= 2) ? m + 12 : m;
        int mp = m_adj - 3;
        int era = (y_adj >= 0 ? y_adj : y_adj - 399) / 400;
        int yoe = y_adj - era * 400;
        int doy = (153 * mp + 2) / 5 + (d - 1);
        int doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
        return era * 146097 + doe - 730485;
    }

    void solver::cc_epoch_to_ymd(int epoch, int& y, int& m, int& d) {
        // Epoch days since 2000-03-01 -> civil (y,m,d) (Hinnant algorithm)
        int z = epoch + 730485;  // absolute days since 0000-03-01
        int era = (z >= 0 ? z : z - 146096) / 146097;
        int doe = z - era * 146097;  // day-of-era [0, 146096]
        // Decompose doe into year-of-era
        int q100 = doe / 36524;
        if (q100 > 3) q100 = 3;  // clamp for last day of 400-year cycle
        int r100 = doe - q100 * 36524;
        int q4 = r100 / 1461;
        int r4 = r100 % 1461;
        int q1 = r4 / 365;
        if (q1 > 3) q1 = 3;  // clamp for last day of 4-year cycle
        int r1 = r4 - q1 * 365;  // day-of-year [0, 365]
        int yoe = q100 * 100 + q4 * 4 + q1;
        int y_march = era * 400 + yoe;  // March-based year
        int mp = (5 * r1 + 2) / 153;
        d = r1 - (153 * mp + 2) / 5 + 1;
        int m_raw = mp + 3;
        m = (m_raw > 12) ? m_raw - 12 : m_raw;
        y = (m <= 2) ? y_march + 1 : y_march;
    }

    void solver::cc_date_add(int dy, int dm, int dd, int py, int pm, int pd,
                              int& ry, int& rm, int& rd) {
        // Step 1: month normalization
        int raw_m = dm + py * 12 + pm;
        int t = raw_m - 1;
        // Euclidean div/mod (matching Z3 semantics: mod >= 0 for positive divisor)
        int q = (t >= 0) ? t / 12 : (t - 11) / 12;
        int r = t - q * 12;
        int ny = dy + q;
        int nm = r + 1;
        // Step 2: EOM clamp
        int dim = cc_days_in_month(ny, nm);
        int cd = (dd > dim) ? dim : dd;
        if (cd < 1) cd = 1;
        // Step 3: day carry via epoch
        if (pd == 0) {
            ry = ny; rm = nm; rd = cd;
        } else {
            int ep = cc_ymd_to_epoch(ny, nm, cd) + pd;
            cc_epoch_to_ymd(ep, ry, rm, rd);
        }
    }

    bool solver::try_concrete_date_add(expr* term, expr* d, expr* p, bool negate_period) {
        // Check if d is date.mk with numeral args and p is period.mk with numeral args
        rational v;
        int dy, dm, dd, py, pm, pd;

        // Extract date components
        if (m_plugin.is_mk_date(d)) {
            app* da = to_app(d);
            if (!m_autil.is_numeral(da->get_arg(0), v)) return false;
            dy = v.get_int32();
            if (!m_autil.is_numeral(da->get_arg(1), v)) return false;
            dm = v.get_int32();
            if (!m_autil.is_numeral(da->get_arg(2), v)) return false;
            dd = v.get_int32();
        } else {
            return false;
        }

        // Extract period components
        if (m_plugin.is_mk_period(d)) {
            // d is actually a period — shouldn't happen, but guard
            return false;
        }
        if (m_plugin.is_mk_period(p)) {
            app* pa = to_app(p);
            if (!m_autil.is_numeral(pa->get_arg(0), v)) return false;
            py = v.get_int32();
            if (!m_autil.is_numeral(pa->get_arg(1), v)) return false;
            pm = v.get_int32();
            if (!m_autil.is_numeral(pa->get_arg(2), v)) return false;
            pd = v.get_int32();
        } else {
            return false;
        }

        if (negate_period) { py = -py; pm = -pm; pd = -pd; }

        int ry, rm, rd;
        cc_date_add(dy, dm, dd, py, pm, pd, ry, rm, rd);

        // Assert: result = date.mk(ry, rm, rd)
        app_ref result = mk_mk_date(m_autil.mk_int(ry), m_autil.mk_int(rm), m_autil.mk_int(rd));
        assert_eq_axiom(term, result);
        // Selectors follow from mk_date axioms (axiomatize_mk_date will fire on the result)
        return true;
    }

    void solver::assert_date_validity(expr* y, expr* mo, expr* d) {
        // Calendar validity: month in [1,12], day in [1, days_in_month(y,mo)].
        // No year bounds — the theory accepts any integer year.
        add_unit(mk_literal(m_autil.mk_le(m_autil.mk_int(1), mo)));
        add_unit(mk_literal(m_autil.mk_le(mo, m_autil.mk_int(12))));
        add_unit(mk_literal(m_autil.mk_le(m_autil.mk_int(1), d)));
        add_unit(mk_literal(m_autil.mk_le(d, mk_days_in_month(y, mo))));
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
        // Selector axioms
        assert_eq_axiom(mk_date_year(term),  y);
        assert_eq_axiom(mk_date_month(term), mo);
        assert_eq_axiom(mk_date_day(term),   d);
        // Validate directly against the raw constructor arguments.
        // When y/mo/d are concrete literals (the common case), the arithmetic
        // solver evaluates e.g. "13 ≤ 12" immediately without waiting for the
        // EUF→arithmetic equality propagation chain that would be needed if we
        // constrained the selector terms (date.month(term)) instead.
        // Coarse bound first for cheap early cutting, then exact days_in_month.
        add_unit(mk_literal(m_autil.mk_le(m_autil.mk_int(1), mo)));
        add_unit(mk_literal(m_autil.mk_le(mo, m_autil.mk_int(12))));
        add_unit(mk_literal(m_autil.mk_le(m_autil.mk_int(1), d)));
        add_unit(mk_literal(m_autil.mk_le(d, m_autil.mk_int(31))));
        assert_date_validity(y, mo, d);
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

        // Fast path: if all inputs are concrete, compute in C++
        if (try_concrete_date_add(term, d, p, false))
            return;

        // Extract components
        app_ref dy = mk_date_year(d);
        app_ref dm = mk_date_month(d);
        app_ref dd = mk_date_day(d);
        app_ref py = mk_period_years(p);
        app_ref pm = mk_period_months(p);
        app_ref pd = mk_period_days(p);

        // Step 1: Month normalization
        expr_ref total_period_months(m_autil.mk_add(m_autil.mk_mul(py, m_autil.mk_int(12)), pm), m);
        expr_ref raw_m(m_autil.mk_add(dm, total_period_months), m);
        expr_ref ny(m), nm(m);
        mk_normalize_month(dy, raw_m, ny, nm);

        // Step 2: EOM clamp
        expr_ref cd = mk_eom_clamp(ny, nm, dd);

        // Check if days(p) is concretely zero — skip epoch conversion
        rational pd_val;
        bool pd_is_zero = m_autil.is_numeral(pd, pd_val) && pd_val.is_zero();

        expr_ref ry(m), rm(m), rd(m);
        if (pd_is_zero) {
            // No day carry needed — result is just (ny, nm, cd)
            ry = ny; rm = nm; rd = cd;
        } else {
            // Step 3: Day addition via epoch conversion
            expr_ref base_epoch = mk_ymd_to_epoch(ny, nm, cd);
            expr_ref result_epoch(m_autil.mk_add(base_epoch, pd), m);
            mk_epoch_to_ymd(result_epoch, ry, rm, rd);
        }

        // Assert result selectors
        assert_eq_axiom(mk_date_year(term), ry);
        assert_eq_axiom(mk_date_month(term), rm);
        assert_eq_axiom(mk_date_day(term), rd);

        // Validity on result
        assert_date_validity(ry, rm, rd);
    }

    void solver::axiomatize_date_sub(expr* term) {
        if (has_axiom(term)) return;
        mark_axiomatized(term);
        app* a = to_app(term);
        expr* d = a->get_arg(0);
        expr* p = a->get_arg(1);

        // Fast path: if all inputs are concrete, compute in C++
        if (try_concrete_date_add(term, d, p, true))
            return;

        // date.sub(d, p) = date.add(d, -p)
        app_ref py = mk_period_years(p);
        app_ref pm = mk_period_months(p);
        app_ref pd = mk_period_days(p);

        // Negate period components
        expr_ref neg_py(m_autil.mk_uminus(py), m);
        expr_ref neg_pm(m_autil.mk_uminus(pm), m);
        expr_ref neg_pd(m_autil.mk_uminus(pd), m);

        // Same logic as date.add with negated period
        app_ref dy = mk_date_year(d);
        app_ref dm = mk_date_month(d);
        app_ref dd = mk_date_day(d);

        // Month normalization
        expr_ref total_period_months(m_autil.mk_add(m_autil.mk_mul(neg_py, m_autil.mk_int(12)), neg_pm), m);
        expr_ref raw_m(m_autil.mk_add(dm, total_period_months), m);
        expr_ref ny(m), nm(m);
        mk_normalize_month(dy, raw_m, ny, nm);

        // EOM clamp
        expr_ref cd = mk_eom_clamp(ny, nm, dd);

        // Check if days(p) is concretely zero — skip epoch conversion
        rational pd_val;
        bool pd_is_zero = m_autil.is_numeral(pd, pd_val) && pd_val.is_zero();

        expr_ref ry(m), rm(m), rd(m);
        if (pd_is_zero) {
            ry = ny; rm = nm; rd = cd;
        } else {
            expr_ref base_epoch = mk_ymd_to_epoch(ny, nm, cd);
            expr_ref result_epoch(m_autil.mk_add(base_epoch, neg_pd), m);
            mk_epoch_to_ymd(result_epoch, ry, rm, rd);
        }

        assert_eq_axiom(mk_date_year(term), ry);
        assert_eq_axiom(mk_date_month(term), rm);
        assert_eq_axiom(mk_date_day(term), rd);

        assert_date_validity(ry, rm, rd);
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

        // Get components
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

        // Lexicographic comparison on (year, month, day) — correct for valid dates
        // ly = (y1 < y2), ey = (y1 == y2), lm = (m1 < m2), em = (m1 == m2), ld/led
        // cmp = ly || (ey && (lm || (em && ld)))
        expr_ref ly(m), lm(m), ld(m);
        expr_ref ey(m.mk_eq(y1, y2), m);
        expr_ref em(m.mk_eq(mo1, mo2), m);

        switch (k) {
        case OP_DATE_LT:
            ly = m.mk_not(m_autil.mk_le(y2, y1));   // y1 < y2
            lm = m.mk_not(m_autil.mk_le(mo2, mo1)); // m1 < m2
            ld = m.mk_not(m_autil.mk_le(dy2, dy1));  // d1 < d2
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
        app_ref y = mk_date_year(e);
        app_ref mo = mk_date_month(e);
        app_ref d = mk_date_day(e);
        app_ref rhs = mk_mk_date(y, mo, d);
        assert_eq_axiom(e, rhs);
        // Validity constraints on free date variables
        assert_date_validity(y, mo, d);
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
        if (!m_plugin.is_date(s) && !m_plugin.is_period(s))
            return;
        mk_var(n);
        // Eagerly axiomatize constructor terms the moment their enode is created,
        // even when they appear only as subterms of a plain EUF equality
        // (e.g. (= d (date.mk 2000 13 1))).  In that case visit_rec / post_visit
        // is never called by the SAT solver, so without this hook the validity
        // constraints would be deferred to check() — too late for the arithmetic
        // theory to propagate the conflict before the solver reports sat.
        expr* e = n->get_expr();
        if (!is_app(e)) return;
        decl_kind k = to_app(e)->get_decl()->get_decl_kind();
        if (k == OP_DATE_MK)
            axiomatize_mk_date(e);
        else if (k == OP_DATE_ADD)
            axiomatize_date_add(e);
        else if (k == OP_DATE_SUB)
            axiomatize_date_sub(e);
        else if (k == OP_PERIOD_ADD)
            axiomatize_period_add(e);
        else if (k == OP_PERIOD_SUB)
            axiomatize_period_sub(e);
        else if (k == OP_PERIOD_MUL)
            axiomatize_period_mul(e);
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
                // For date.mk constructors, axiomatize_mk_date validates
                // directly against the raw integer arguments so the arithmetic
                // solver can catch e.g. month=13 without waiting for EUF
                // equality propagation (which never fires when the constructor
                // appears only inside a plain EUF equality like (= d (date.mk ...))).
                if (is_app(ex) && to_app(ex)->get_decl()->get_decl_kind() == OP_DATE_MK)
                    axiomatize_mk_date(ex);
                else
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
