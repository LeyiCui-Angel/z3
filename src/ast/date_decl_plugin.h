/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Declarations for the theory of calendar dates.

    The theory introduces the sort Date together with

      date.mk    : Int Int Int -> Date        (constructor)
      date.year  : Date -> Int                (selectors)
      date.month : Date -> Int
      date.day   : Date -> Int
      date.add   : Date Int Int Int -> Date   (period arithmetic)
      date.sub   : Date Int Int Int -> Date
      date.lt    : Date Date -> Bool          (lexicographic comparisons)
      date.le    : Date Date -> Bool
      date.gt    : Date Date -> Bool
      date.ge    : Date Date -> Bool

    Date values denote calendar-valid dates in the proleptic Gregorian
    calendar with unbounded years. Applications of date.mk to invalid
    triples are well-sorted, but their value is unspecified.

Author:

    Claude 2026-07-04

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
    // internal: day number (rata die) of a date; not exposed to the SMT-LIB
    // front-end. Used by the theory solvers to reduce date constraints to
    // integer arithmetic.
    OP_DATE_RATA,
    LAST_DATE_OP
};

class date_decl_plugin : public decl_plugin {
    sort* m_date { nullptr };
    sort* m_int { nullptr };

    void set_manager(ast_manager * m, family_id id) override;

    func_decl* mk_date_op(decl_kind k, unsigned arity, sort* const* domain);

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
    ast_manager& m;
    arith_util   m_arith;
    family_id    m_fid;

public:
    date_util(ast_manager& m):
        m(m),
        m_arith(m),
        m_fid(m.mk_family_id("date")) {}

    ast_manager& get_manager() const { return m; }
    arith_util& arith() { return m_arith; }
    family_id get_family_id() const { return m_fid; }

    sort* mk_date_sort() { return m.mk_sort(m_fid, DATE_SORT); }
    bool is_date(sort* s) const { return is_sort_of(s, m_fid, DATE_SORT); }
    bool is_date(expr* e) const { return is_date(e->get_sort()); }

    app* mk_mk(expr* y, expr* mo, expr* d) { expr* args[3] = { y, mo, d }; return m.mk_app(m_fid, OP_DATE_MK, 3, args); }
    app* mk_year(expr* d)  { return m.mk_app(m_fid, OP_DATE_YEAR, d); }
    app* mk_month(expr* d) { return m.mk_app(m_fid, OP_DATE_MONTH, d); }
    app* mk_day(expr* d)   { return m.mk_app(m_fid, OP_DATE_DAY, d); }
    app* mk_lt(expr* a, expr* b) { return m.mk_app(m_fid, OP_DATE_LT, a, b); }
    app* mk_le(expr* a, expr* b) { return m.mk_app(m_fid, OP_DATE_LE, a, b); }
    app* mk_rata(expr* d) { return m.mk_app(m_fid, OP_DATE_RATA, d); }

    bool is_mk(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_MK); }
    bool is_year(expr const* e)  const { return is_app_of(e, m_fid, OP_DATE_YEAR); }
    bool is_month(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_MONTH); }
    bool is_day(expr const* e)   const { return is_app_of(e, m_fid, OP_DATE_DAY); }
    bool is_add(expr const* e)   const { return is_app_of(e, m_fid, OP_DATE_ADD); }
    bool is_sub(expr const* e)   const { return is_app_of(e, m_fid, OP_DATE_SUB); }
    bool is_lt(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_LT); }
    bool is_le(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_LE); }
    bool is_gt(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_GT); }
    bool is_ge(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_GE); }
    bool is_rata(expr const* e)  const { return is_app_of(e, m_fid, OP_DATE_RATA); }

    // e is (date.mk y m d) with numeral arguments; the triple need not be valid.
    bool is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d) const;

    // e is a canonical Date value: numeral date.mk with a calendar-valid triple.
    bool is_value_mk(expr const* e, rational& y, rational& mo, rational& d) const {
        return is_numeral_mk(e, y, mo, d) && is_valid_date(y, mo, d);
    }

    app* mk_date_value(rational const& y, rational const& mo, rational const& d);

    // --- concrete Gregorian calendar arithmetic -------------------------

    static bool is_leap_year(rational const& y);
    static rational days_in_month(rational const& y, rational const& mo);
    static bool is_valid_date(rational const& y, rational const& mo, rational const& d);

    // days since 1970-01-01 (Howard Hinnant's days_from_civil, unbounded)
    static rational rata_die(rational const& y, rational const& mo, rational const& d);
    // inverse of rata_die (civil_from_days)
    static void date_of_rata_die(rational const& rd, rational& y, rational& mo, rational& d);

    // fixed total interpretation of date.mk on numeral triples: normalizes
    // any integer triple to a calendar-valid date (identity on valid input).
    // Refines the intentionally unspecified behavior of invalid direct
    // constructor applications deterministically, so that rewriter, theory
    // solvers and model evaluation agree on one value.
    static void normalize_mk(rational& y, rational& mo, rational& d);

    // the date.add algorithm on a valid concrete date:
    // month normalization, end-of-month clamp, day carry
    static void add_period(rational const& y, rational const& mo, rational const& d,
                           rational const& py, rational const& pm, rational const& pd,
                           rational& ry, rational& rm, rational& rd);

    // --- symbolic axiom building blocks ---------------------------------
    // Integer/Boolean terms mirroring the concrete functions above; used by
    // the theory solvers to reduce date constraints to integer arithmetic.

    expr_ref mk_is_leap_expr(expr* y);
    expr_ref mk_days_in_month_expr(expr* y, expr* mo);
    expr_ref mk_valid_expr(expr* y, expr* mo, expr* d);
    expr_ref mk_rata_die_expr(expr* y, expr* mo, expr* d);
    // steps 1 and 2 of the date.add algorithm: month normalization of
    // (y, mo) by (py, pm) followed by the end-of-month clamp of d
    void mk_add_normalize_exprs(expr* y, expr* mo, expr* d, expr* py, expr* pm,
                                expr_ref& out_y, expr_ref& out_m, expr_ref& out_d);
};
