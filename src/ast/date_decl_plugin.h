/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Declaration plugin for the theory of calendar dates.

    The theory introduces the sort Date of calendar-valid proleptic
    Gregorian dates together with:

      - constructor  date.mk : Int Int Int -> Date
      - selectors    date.year, date.month, date.day : Date -> Int
      - arithmetic   date.add, date.sub : Date Int Int Int -> Date
      - comparisons  date.lt, date.le, date.gt, date.ge : Date Date -> Bool

    date.mk is total at the SMT-LIB level. Its behavior is specified
    only for calendar-valid triples; applications to invalid triples
    are well-sorted but denote an unspecified (valid) date.

Author:

    Date theory extension 2026-07-05

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
    sort* m_int  { nullptr };

    void set_manager(ast_manager * m, family_id id) override;

    func_decl* mk_decl(decl_kind k, unsigned arity, sort* const* domain);

public:
    char const* date_sort_name() const { return "Date"; }

    void finalize() override;

    decl_plugin* mk_fresh() override { return alloc(date_decl_plugin); }

    sort* mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override;

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
        unsigned arity, sort* const* domain, sort* range) override;

    void get_op_names(svector<builtin_name>& op_names, symbol const& logic) override;

    void get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) override;

    bool is_value(app* e) const override;

    bool is_unique_value(app* e) const override;

    expr* get_some_value(sort* s) override;

    sort* date_sort() const { return m_date; }

    sort* int_sort() const { return m_int; }
};

/**
   \brief Utility for constructing and recognizing date terms, and for
   concrete Gregorian calendar computations over unbounded integers.
*/
class date_util {
    ast_manager&      m;
    date_decl_plugin* m_plugin;
    family_id         m_fid;
    arith_util        m_arith;

public:
    date_util(ast_manager& m);

    ast_manager& get_manager() const { return m; }
    family_id get_family_id() const { return m_fid; }
    date_decl_plugin& plugin() const { return *m_plugin; }
    arith_util& arith() { return m_arith; }

    sort* mk_date_sort() const { return m_plugin->date_sort(); }
    bool is_date(sort const* s) const { return is_sort_of(s, m_fid, DATE_SORT); }
    bool is_date(expr const* e) const { return is_date(e->get_sort()); }

    app* mk_mk(expr* y, expr* mo, expr* d) { expr* args[3] = { y, mo, d }; return m.mk_app(m_fid, OP_DATE_MK, 3, args); }
    app* mk_year(expr* d) { return m.mk_app(m_fid, OP_DATE_YEAR, d); }
    app* mk_month(expr* d) { return m.mk_app(m_fid, OP_DATE_MONTH, d); }
    app* mk_day(expr* d) { return m.mk_app(m_fid, OP_DATE_DAY, d); }
    app* mk_add(expr* d, expr* py, expr* pm, expr* pd) { expr* args[4] = { d, py, pm, pd }; return m.mk_app(m_fid, OP_DATE_ADD, 4, args); }
    app* mk_sub(expr* d, expr* py, expr* pm, expr* pd) { expr* args[4] = { d, py, pm, pd }; return m.mk_app(m_fid, OP_DATE_SUB, 4, args); }
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

    MATCH_TERNARY(is_mk);
    MATCH_UNARY(is_year);
    MATCH_UNARY(is_month);
    MATCH_UNARY(is_day);
    MATCH_BINARY(is_lt);
    MATCH_BINARY(is_le);
    MATCH_BINARY(is_gt);
    MATCH_BINARY(is_ge);

    /**
       \brief Build the canonical value term (date.mk y mo d) with integer numerals.
    */
    app* mk_date_value(rational const& y, rational const& mo, rational const& d);

    /**
       \brief Recognize (date.mk n1 n2 n3) with integer numeral arguments.
       Does not require the triple to be calendar-valid.
    */
    bool is_date_numeral(expr* e, rational& y, rational& mo, rational& d) const;

    /**
       \brief Recognize a canonical Date value: numeral triple that is calendar-valid.
    */
    bool is_date_value(expr* e, rational& y, rational& mo, rational& d) const;

    // ------------------------------------------------------------------
    // Concrete proleptic Gregorian calendar arithmetic.

    static bool is_leap_year(rational const& y);
    static rational days_in_month(rational const& y, rational const& mo);
    static bool is_valid_date(rational const& y, rational const& mo, rational const& d);

    /**
       \brief Number of days since the civil epoch 1970-01-01 (rata die style
       bijection between calendar-valid dates and the integers).
    */
    static rational days_from_civil(rational const& y, rational const& mo, rational const& d);

    /**
       \brief Inverse of days_from_civil.
    */
    static void civil_from_days(rational const& n, rational& y, rational& mo, rational& d);

    /**
       \brief Apply the three-step date.add algorithm (month normalization,
       end-of-month clamp, day carry) to the valid date (y, mo, d).
    */
    static void add_period(rational& y, rational& mo, rational& d,
                           rational const& py, rational const& pm, rational const& pd);
};
