/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Declaration plugin for the theory of calendar dates.

    The theory introduces one sort, Date, together with a constructor,
    selectors, date arithmetic and chronological comparisons:

        (date.mk    Int Int Int Date)      ; year month day
        (date.year  Date Int)
        (date.month Date Int)
        (date.day   Date Int)
        (date.add   Date Int Int Int Date) ; d py pm pd
        (date.sub   Date Int Int Int Date) ; d py pm pd
        (date.lt    Date Date Bool)
        (date.le    Date Date Bool)
        (date.gt    Date Date Bool)
        (date.ge    Date Date Bool)

    Semantics
    ---------

    Date is interpreted as the set of days of the proleptic Gregorian
    calendar, extended indefinitely into the past and the future (year
    numbers are arbitrary integers, using astronomical numbering, so year
    0 exists and is a leap year). This set is in bijection with Int by
    counting days from the epoch 1970-01-01 (day 0). The bijection is
    computed with Howard Hinnant's civil-from-days/days-from-civil
    algorithms, which only use integer division by positive constants,
    so all date reasoning reduces to linear integer arithmetic.

    - (date.mk y m d) is total. The months are first normalized into
      years: y' = y + floor((m - 1)/12), m' = ((m - 1) mod 12) + 1, and
      the result is the day (d - 1) days after the first day of month
      (y', m'). Out-of-range day arguments roll over across month and
      year boundaries (mktime-style), e.g.
          (date.mk 2000 2 30)  = 2000-03-01
          (date.mk 2021 13 1)  = 2022-01-01
          (date.mk 2020 1 0)   = 2019-12-31.

    - date.year/date.month/date.day return the components of the unique
      normalized representation, so for every date value v:
          1 <= (date.month v) <= 12,
          1 <= (date.day v)   <= days-in-month(year v, month v), and
          (date.mk (date.year v) (date.month v) (date.day v)) = v.

    - (date.add d py pm pd) follows the usual convention of calendar
      libraries (java.time, dateutil): first add 12*py + pm months to
      the (year, month) of d, clamp the day-of-month to the length of
      the target month, then add pd days exactly:
          2020-01-31 + (0 1 0) = 2020-02-29 (clamped)
          2019-01-31 + (0 1 0) = 2019-02-28 (clamped)
          2020-02-29 + (1 0 0) = 2021-02-28 (clamped)
      (date.sub d py pm pd) = (date.add d (- py) (- pm) (- pd)).

    - date.lt/le/gt/ge is chronological order; = holds iff two dates
      denote the same calendar day.

    Values of sort Date are represented as (date.mk y m d) applications
    with normalized numeral arguments.

Author:

    Angel Cui's date theory task 2026-07-04

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
    OP_DATE_GE,
    // Internal operator mapping a date to its epoch day number.
    // It is not part of the SMT-LIB signature of the theory and is
    // only created by the theory solvers.
    OP_DATE_EPOCH
};

class date_decl_plugin : public decl_plugin {
    sort* m_date { nullptr };

    void set_manager(ast_manager* m, family_id id) override;

    func_decl* mk_decl(decl_kind k, char const* name, unsigned arity, sort* const* domain, sort* range);

public:
    date_decl_plugin() = default;

    ~date_decl_plugin() override;

    void finalize() override {}

    decl_plugin* mk_fresh() override { return alloc(date_decl_plugin); }

    sort* mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override { return m_date; }

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
        unsigned arity, sort* const* domain, sort* range) override;

    void get_op_names(svector<builtin_name>& op_names, symbol const& logic) override;

    void get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) override;

    bool is_value(app* e) const override;

    bool is_unique_value(app* e) const override;

    bool are_equal(app* a, app* b) const override { return a == b; }

    bool are_distinct(app* a, app* b) const override;

    expr* get_some_value(sort* s) override;

    sort* date_sort() const { return m_date; }

    // --- concrete calendar arithmetic (proleptic Gregorian) ---

    static bool is_leap_year(rational const& y);

    // number of days of month mo (in [1..12]) of year y
    static rational days_in_month(rational const& y, rational const& mo);

    // normalize a (year, month) pair such that mo is in [1..12]
    static void normalize_ym(rational& y, rational& mo);

    // epoch day number of (date.mk y mo d); (y, mo, d) need not be normalized
    static rational civil_to_days(rational y, rational mo, rational const& d);

    // inverse of civil_to_days restricted to normalized triples
    static void days_to_civil(rational const& n, rational& y, rational& mo, rational& d);

    // epoch day number of (date.add d py pm pd) where n is the epoch day number of d
    static rational add_to_days(rational const& n, rational const& py, rational const& pm, rational const& pd);
};

class date_util {
    ast_manager&      m;
    arith_util        m_arith;
    date_decl_plugin* m_plugin;
    family_id         m_fid;

    app* mk_fresh_int(char const* prefix);

    // fresh integer constant equated with def and bounded by [lo, hi];
    // the explicit bounds sharpen the arithmetic solver's relaxation
    expr_ref bind_int(char const* prefix, expr* def, int lo, int hi, expr_ref_vector& constraints);

    // Fresh integer constants and constraints computing 365*y + (number of
    // leap years before year y) + 1 (days from 0000-01-01 to y-01-01, plus 1).
    // leap01 is set to a 0/1 term that is 1 iff y is a leap year.
    expr_ref mk_year_days(expr* y, expr_ref& leap01, expr_ref_vector& constraints);

    // days in the months before month mo (mo in [1..12]) of a year with leap indicator leap01
    expr_ref mk_month_offset(expr* mo, expr* leap01);

    // number of days of month mo (mo in [1..12]) of a year with leap indicator leap01
    expr_ref mk_days_in_month(expr* mo, expr* leap01);

    // Fresh (y2, m2) normalizing the zero-based month count expressed by months:
    // 12*y2 + (m2 - 1) = months and m2 in [1..12].
    void mk_norm_month(expr* months, expr_ref& y2, expr_ref& m2, expr_ref_vector& constraints);

public:
    date_util(ast_manager& m);

    ast_manager& get_manager() const { return m; }
    arith_util& arith() { return m_arith; }
    date_decl_plugin& plugin() const { return *m_plugin; }
    family_id get_family_id() const { return m_fid; }

    sort* mk_date_sort() const { return m_plugin->date_sort(); }
    bool is_date(sort* s) const { return s == m_plugin->date_sort(); }
    bool is_date(expr const* e) const { return is_date(e->get_sort()); }

    app* mk_mk(expr* y, expr* mo, expr* d) { expr* args[3] = { y, mo, d }; return m.mk_app(m_fid, OP_DATE_MK, 3, args); }
    app* mk_year(expr* d) { return m.mk_app(m_fid, OP_DATE_YEAR, d); }
    app* mk_month(expr* d) { return m.mk_app(m_fid, OP_DATE_MONTH, d); }
    app* mk_day(expr* d) { return m.mk_app(m_fid, OP_DATE_DAY, d); }
    app* mk_lt(expr* a, expr* b) { return m.mk_app(m_fid, OP_DATE_LT, a, b); }
    app* mk_le(expr* a, expr* b) { return m.mk_app(m_fid, OP_DATE_LE, a, b); }
    app* mk_epoch(expr* d) { return m.mk_app(m_fid, OP_DATE_EPOCH, d); }

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
    bool is_epoch(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_EPOCH); }

    MATCH_UNARY(is_year);
    MATCH_UNARY(is_month);
    MATCH_UNARY(is_day);
    MATCH_UNARY(is_epoch);
    MATCH_BINARY(is_lt);
    MATCH_BINARY(is_le);
    MATCH_BINARY(is_gt);
    MATCH_BINARY(is_ge);

    // (date.mk y mo d) with integer numeral arguments; the triple need not be normalized
    bool is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d);

    // normalized date value with the given epoch day number
    app* mk_value_from_epoch(rational const& n);

    // --- symbolic epoch encodings ---
    //
    // The encodings are relational: they introduce fresh integer constants
    // related to the inputs by linear constraints with explicitly bounded
    // remainder variables (appended to the constraints vector). This form
    // avoids nested integer divisions and keeps the arithmetic solver's
    // branching bounded.

    // Constrain fresh integer constants (y, mo, d) to range over the civil
    // representations of dates, and return the term computing the epoch day
    // number of (y, mo, d). Equating the result with an epoch term makes
    // (y, mo, d) the civil components of that date.
    expr_ref mk_civil_rep(expr_ref& y, expr_ref& mo, expr_ref& d, expr_ref_vector& constraints);

    // epoch day number of (date.mk y mo d) for arbitrary integer terms
    expr_ref mk_epoch_of_ymd(expr* y, expr* mo, expr* d, expr_ref_vector& constraints);

    // epoch day number of (date.add d py pm pd) (or date.sub if sub is true),
    // where (y0, mo0, d0) are the civil components of d
    expr_ref mk_epoch_add(expr* y0, expr* mo0, expr* d0, expr* py, expr* pm, expr* pd, bool sub,
                          expr_ref_vector& constraints);
};
