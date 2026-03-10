/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Native theory of calendar dates and periods for Z3.

    Sorts:
        Date   - calendar dates
        Period - (years, months, days) triples

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"

enum date_sort_kind {
    DATE_SORT,
    PERIOD_SORT
};

enum date_op_kind {
    OP_DATE_MK,          // mk-date(year: Int, month: Int, day: Int) -> Date
    OP_PERIOD_MK,        // mk-period(years: Int, months: Int, days: Int) -> Period
    OP_DATE_YEAR,        // date-year(d: Date) -> Int
    OP_DATE_MONTH,       // date-month(d: Date) -> Int
    OP_DATE_DAY,         // date-day(d: Date) -> Int
    OP_PERIOD_YEARS,     // p-years(p: Period) -> Int
    OP_PERIOD_MONTHS,    // p-months(p: Period) -> Int
    OP_PERIOD_DAYS,      // p-days(p: Period) -> Int
    OP_DATE_ADD,         // date_add(d: Date, p: Period) -> Date
    OP_DATE_SUB,         // date_sub(d: Date, p: Period) -> Date
    OP_DATE_LT,          // date_lt(d1: Date, d2: Date) -> Bool
    OP_DATE_LE,          // date_le(d1: Date, d2: Date) -> Bool
    OP_DATE_GT,          // date_gt(d1: Date, d2: Date) -> Bool
    OP_DATE_GE,          // date_ge(d1: Date, d2: Date) -> Bool
    OP_PERIOD_ADD,       // period_add(p1: Period, p2: Period) -> Period
    OP_PERIOD_SUB,       // period_sub(p1: Period, p2: Period) -> Period
    OP_PERIOD_MUL,       // period_mul(p: Period, k: Int) -> Period
    LAST_DATE_OP
};

class date_decl_plugin : public decl_plugin {
    sort* m_date_sort  { nullptr };
    sort* m_period_sort { nullptr };

    sort* int_sort() const;
    bool is_int_sort(sort* s) const;

    void set_manager(ast_manager * m, family_id id) override;

public:
    date_decl_plugin();
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

    sort* date_sort() const { return m_date_sort; }
    sort* period_sort() const { return m_period_sort; }

    app* mk_default_date(ast_manager& m) const;
    app* mk_default_period(ast_manager& m) const;

    // Recognizers
    bool is_date(sort const* s) const { return is_sort_of(s, m_family_id, DATE_SORT); }
    bool is_period(sort const* s) const { return is_sort_of(s, m_family_id, PERIOD_SORT); }
    bool is_date(expr const* e) const { return is_date(e->get_sort()); }
    bool is_period(expr const* e) const { return is_period(e->get_sort()); }

    bool is_mk_date(expr const* e) const { return is_app_of(e, m_family_id, OP_DATE_MK); }
    bool is_mk_period(expr const* e) const { return is_app_of(e, m_family_id, OP_PERIOD_MK); }

    bool is_date_year(expr const* e) const { return is_app_of(e, m_family_id, OP_DATE_YEAR); }
    bool is_date_month(expr const* e) const { return is_app_of(e, m_family_id, OP_DATE_MONTH); }
    bool is_date_day(expr const* e) const { return is_app_of(e, m_family_id, OP_DATE_DAY); }

    bool is_date_add(expr const* e) const { return is_app_of(e, m_family_id, OP_DATE_ADD); }
    bool is_date_sub(expr const* e) const { return is_app_of(e, m_family_id, OP_DATE_SUB); }
    bool is_date_lt(expr const* e) const { return is_app_of(e, m_family_id, OP_DATE_LT); }
    bool is_date_le(expr const* e) const { return is_app_of(e, m_family_id, OP_DATE_LE); }
    bool is_date_gt(expr const* e) const { return is_app_of(e, m_family_id, OP_DATE_GT); }
    bool is_date_ge(expr const* e) const { return is_app_of(e, m_family_id, OP_DATE_GE); }

    bool is_period_years(expr const* e) const { return is_app_of(e, m_family_id, OP_PERIOD_YEARS); }
    bool is_period_months(expr const* e) const { return is_app_of(e, m_family_id, OP_PERIOD_MONTHS); }
    bool is_period_days(expr const* e) const { return is_app_of(e, m_family_id, OP_PERIOD_DAYS); }

    bool is_period_add(expr const* e) const { return is_app_of(e, m_family_id, OP_PERIOD_ADD); }
    bool is_period_sub(expr const* e) const { return is_app_of(e, m_family_id, OP_PERIOD_SUB); }
    bool is_period_mul(expr const* e) const { return is_app_of(e, m_family_id, OP_PERIOD_MUL); }
};
