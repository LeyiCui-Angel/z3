/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Declarations for the theory of calendar dates.

    The theory introduces the sort Date together with a constructor
    date.mk, selectors date.year, date.month, date.day, calendar
    arithmetic date.add, date.sub, and the lexicographic comparisons
    date.lt, date.le, date.gt, date.ge.

    Date values denote calendar-valid dates in the proleptic Gregorian
    calendar with unbounded integer years. The constructor date.mk is
    total at the term level: applications to invalid triples are
    well-sorted, but their meaning is unspecified.

Author:

    Angel Cui 2026-03-23

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"

enum date_sort_kind {
    DATE_SORT
};

enum date_op_kind {
    OP_DATE_MK,
    OP_DATE_YEAR,
    OP_DATE_MONTH,
    OP_DATE_DAY,
    OP_DATE_ADD,
    OP_DATE_SUB,
    OP_DATE_LT,
    OP_DATE_LE,
    OP_DATE_GT,
    OP_DATE_GE
};

class date_decl_plugin : public decl_plugin {
    sort* m_date { nullptr };
    sort* m_int { nullptr };

    void set_manager(ast_manager* m, family_id id) override;

    func_decl* mk_date_op(decl_kind k, char const* name, unsigned arity, sort* const* domain, sort* range);

public:
    date_decl_plugin() = default;

    ~date_decl_plugin() override;

    void finalize() override {}

    decl_plugin* mk_fresh() override { return alloc(date_decl_plugin); }

    sort* mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override;

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
        unsigned arity, sort* const* domain, sort* range) override;

    void get_op_names(svector<builtin_name>& op_names, symbol const& logic) override;

    void get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) override;

    bool is_value(app* e) const override;

    bool is_unique_value(app* e) const override;

    bool are_equal(app* a, app* b) const override;

    bool are_distinct(app* a, app* b) const override;

    expr* get_some_value(sort* s) override;

    sort* date_sort() const { return m_date; }
};

class date_util {
    ast_manager&      m;
    date_decl_plugin* m_plugin;
    family_id         m_fid;
    arith_util        m_arith;

    expr* mk_ge1_le(expr* x, unsigned hi);

public:
    date_util(ast_manager& m);

    ast_manager& get_manager() const { return m; }
    family_id get_family_id() const { return m_fid; }
    arith_util& arith() { return m_arith; }

    sort* mk_date_sort() const { return m_plugin->date_sort(); }
    bool is_date(sort* s) const { return is_sort_of(s, m_fid, DATE_SORT); }
    bool is_date(expr const* e) const { return is_date(e->get_sort()); }

    app* mk_mk(expr* y, expr* mo, expr* d);
    app* mk_year(expr* d) { return m.mk_app(m_fid, OP_DATE_YEAR, d); }
    app* mk_month(expr* d) { return m.mk_app(m_fid, OP_DATE_MONTH, d); }
    app* mk_day(expr* d) { return m.mk_app(m_fid, OP_DATE_DAY, d); }
    app* mk_add(expr* d, expr* py, expr* pm, expr* pd);
    app* mk_lt(expr* a, expr* b) { return m.mk_app(m_fid, OP_DATE_LT, a, b); }
    app* mk_le(expr* a, expr* b) { return m.mk_app(m_fid, OP_DATE_LE, a, b); }

    bool is_mk(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_MK); }
    bool is_year(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_YEAR); }
    bool is_month(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_MONTH); }
    bool is_day(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_DAY); }
    bool is_add(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_ADD); }
    bool is_sub(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_SUB); }
    bool is_lt(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_LT); }
    bool is_le(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_LE); }
    bool is_gt(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_GT); }
    bool is_ge(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_GE); }
    bool is_selector(expr const* e) const { return is_year(e) || is_month(e) || is_day(e); }

    MATCH_UNARY(is_year);
    MATCH_UNARY(is_month);
    MATCH_UNARY(is_day);

    // recognize (date.mk n1 n2 n3) with numeral arguments
    bool is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d) const;
    // recognize (date.mk n1 n2 n3) denoting a calendar-valid date
    bool is_value_mk(expr const* e, rational& y, rational& mo, rational& d) const;
    bool is_value_mk(expr const* e) const;

    // ------------------------------------------------------------------
    // concrete Gregorian calendar arithmetic
    // ------------------------------------------------------------------

    static bool is_leap_year(rational const& y);
    static unsigned days_in_month(rational const& y, unsigned m);
    static bool is_valid_date(rational const& y, rational const& mo, rational const& d);
    // Rata Die day number of a valid date; rata_die(1, 1, 1) = 1.
    static rational rata_die(rational const& y, unsigned mo, rational const& d);
    static void rata_die_inv(rational const& n, rational& y, unsigned& mo, rational& d);
    // the date.add algorithm: month normalization, end-of-month clamp, day carry
    static void add_period(rational const& y, rational const& mo, rational const& d,
                           rational const& py, rational const& pm, rational const& pd,
                           rational& oy, rational& om, rational& od);

    // ------------------------------------------------------------------
    // symbolic axiom building (all in linear integer arithmetic with
    // div/mod by numeric constants)
    // ------------------------------------------------------------------

    // ((y mod 4 = 0) and (y mod 100 != 0)) or (y mod 400 = 0)
    expr_ref mk_is_leap(expr* y);
    // days in month expressed by case analysis on the month
    expr_ref mk_days_in_month(expr* y, expr* mo);
    // 1 <= mo <= 12 and 1 <= d <= days_in_month(y, mo)
    expr_ref mk_is_valid(expr* y, expr* mo, expr* d);
    // Rata Die day number as a term over (y, mo, d)
    expr_ref mk_rata_die(expr* y, expr* mo, expr* d);
    // Rata Die day number of the result of date.add(d, py, pm, pd),
    // given the selector terms of the date argument
    expr_ref mk_add_rata_die(expr* yd, expr* md, expr* dd, expr* py, expr* pm, expr* pd);
    // days in month for a concrete month; only February depends on the year
    expr_ref mk_days_in_month_concrete(expr* y, unsigned mo);
    // the result triple of date.add(d, py, pm, pd) for a concrete period,
    // as a bounded case split over the month and the day carry;
    // requires |pd| <= mk_add_triple_bound()
    void mk_add_triple(expr* yd, expr* md, expr* dd,
                       rational const& py, rational const& pm, rational const& pd,
                       expr_ref& ry, expr_ref& rm, expr_ref& rd);
    static rational mk_add_triple_bound() { return rational(1830); }
};
