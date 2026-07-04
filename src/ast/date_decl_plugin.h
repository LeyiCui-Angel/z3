/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Declarations for the theory of calendar dates.

    The theory introduces the sort Date together with

      - (date.mk Int Int Int Date)                constructor (year month day)
      - (date.year Date Int), (date.month Date Int), (date.day Date Int)
      - (date.add Date Int Int Int Date)          add (year month day) offsets
      - (date.sub Date Int Int Int Date)          subtract (year month day) offsets
      - (date.lt/le/gt/ge Date Date Bool)         calendar order

    Semantics (derived from the accompanying examples of the task setup):

    * Every value of sort Date is a calendar-valid proleptic Gregorian date:
      1 <= month <= 12 and 1 <= day <= days_in_month(year, month), where
      February has 29 days in leap years, i.e. years y with
      (y mod 4 = 0 and y mod 100 != 0) or y mod 400 = 0.
      Years range over all integers (proleptic calendar).

    * date.mk applied to a calendar-valid triple (y, m, d) denotes that date;
      the selectors recover the components. date.mk is total at the SMT-LIB
      level: applied to an invalid triple it denotes an unspecified (but
      consistent) valid date whose components are unrelated to the arguments.

    * (date.add d py pm pd) follows the conventional three step algorithm:
        1. month normalization: t = month(d) + 12*py + pm - 1,
           y1 = year(d) + floor(t / 12), m1 = (t mod 12) + 1
        2. end-of-month clamp: d1 = min(day(d), days_in_month(y1, m1))
        3. day carry: the result is the calendar date pd days after
           (y1, m1, d1), carrying across month and year boundaries.
      (date.sub d py pm pd) = (date.add d (- py) (- pm) (- pd)).

    * date.lt/le/gt/ge compare dates chronologically, which coincides with
      the lexicographic order on (year, month, day). Equality of dates is
      extensional: dates are equal iff their components are equal.

    The day carry and the chronological order are expressed through the
    bijection between valid dates and their epoch day number (days since
    1970-01-01), using H. Hinnant's civil-calendar algorithms. These use
    only integer division by positive constants and are therefore fully
    within linear integer arithmetic.

Author:

    Claude (Anthropic) 2026-07-04

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
    // internal only: epoch day number (days since 1970-01-01) of a date.
    // Not exposed through the SMT-LIB front-end; used by the theory
    // solvers to share the epoch of a date term across axioms.
    OP_DATE_EPOCH
};

class date_decl_plugin : public decl_plugin {
    sort* m_date { nullptr };

    void set_manager(ast_manager * m, family_id id) override;

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

    bool are_distinct(app* a, app* b) const override;

    expr* get_some_value(sort* s) override;

    sort* date_sort() const { return m_date; }
};

/**
   \brief Utility functions for the date theory: recognizers, term builders,
   concrete calendar arithmetic and builders for the arithmetic definitions
   ("specs") of the date operations used by the theory solvers.
*/
class date_util {
    ast_manager&      m;
    arith_util        m_arith;
    date_decl_plugin* m_plugin;
    family_id         m_fid;

    // building blocks with constant folding
    expr_ref num(rational const& v);
    bool     get_num(expr* e, rational& v) const;
    expr_ref fadd(expr* x, expr* y);
    expr_ref fadd(expr* x, rational const& c);
    expr_ref fmul(rational const& c, expr* x);
    expr_ref fidiv(expr* x, rational const& c);
    expr_ref fmod(expr* x, rational const& c);
    expr_ref fle(expr* x, expr* y);
    expr_ref feq(expr* x, expr* y);
    expr_ref fite(expr* c, expr* t, expr* e);

    void mk_days_to_civil(expr* z, expr_ref& y, expr_ref& mo, expr_ref& d);

public:
    date_util(ast_manager& m);

    ast_manager& get_manager() const { return m; }
    family_id get_family_id() const { return m_fid; }
    date_decl_plugin& plugin() const { return *m_plugin; }

    sort* mk_date_sort() const { return m_plugin->date_sort(); }
    bool is_date(sort* s) const { return s == m_plugin->date_sort(); }
    bool is_date(expr* e) const { return is_date(e->get_sort()); }

    app* mk_date(expr* y, expr* mo, expr* d) { expr* args[3] = { y, mo, d }; return m.mk_app(m_fid, OP_DATE_MK, 3, args); }
    app* mk_date(rational const& y, rational const& mo, rational const& d);
    app* mk_year(expr* d) { return m.mk_app(m_fid, OP_DATE_YEAR, d); }
    app* mk_month(expr* d) { return m.mk_app(m_fid, OP_DATE_MONTH, d); }
    app* mk_day(expr* d) { return m.mk_app(m_fid, OP_DATE_DAY, d); }
    app* mk_epoch_term(expr* d) { return m.mk_app(m_fid, OP_DATE_EPOCH, d); }

    bool is_mk(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_MK); }
    bool is_year(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_YEAR); }
    bool is_month(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_MONTH); }
    bool is_day(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_DAY); }
    bool is_add(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_ADD); }
    bool is_sub(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_SUB); }
    bool is_epoch(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_EPOCH); }
    bool is_lt(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_LT); }
    bool is_le(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_LE); }
    bool is_gt(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_GT); }
    bool is_ge(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_GE); }
    bool is_comparison(expr const* e) const { return is_lt(e) || is_le(e) || is_gt(e) || is_ge(e); }

    // \brief recognize (date.mk y m d) with integer numeral arguments.
    bool is_concrete_mk(expr const* e, rational& y, rational& mo, rational& d) const;
    // \brief concretely evaluate a ground date term: a calendar-valid
    // concrete date.mk application, or date.add/date.sub with numeral
    // offsets applied to a ground date term.
    bool eval_ground(expr const* e, rational& y, rational& mo, rational& d) const;
    // \brief recognize (date.mk y m d) with numeral arguments forming a valid date.
    bool is_value(expr const* e) const;

    // concrete calendar arithmetic
    static bool is_leap_year(rational const& y);
    static rational days_in_month(rational const& y, rational const& mo);
    static bool is_valid_date(rational const& y, rational const& mo, rational const& d);
    // days since 1970-01-01 of the valid date (y, mo, d)
    static rational civil_to_days(rational const& y, rational const& mo, rational const& d);
    // valid date z days after 1970-01-01
    static void days_to_civil(rational const& z, rational& y, rational& mo, rational& d);
    // the three step add/sub algorithm on a valid date; sub is add with negated offsets
    static void add_period(rational const& y, rational const& mo, rational const& d,
                           rational const& py, rational const& pm, rational const& pd,
                           rational& ry, rational& rm, rational& rd);

    // symbolic builders (constant folding when arguments are numerals)
    expr_ref mk_is_leap(expr* y);
    expr_ref mk_days_in_month(expr* y, expr* mo);
    expr_ref mk_is_valid(expr* y, expr* mo, expr* d);
    expr_ref mk_civil_to_days(expr* y, expr* mo, expr* d);

    // components of a date term: numerals for a calendar-valid concrete
    // date.mk application, the selector terms otherwise
    void components(expr* d, expr_ref& y, expr_ref& mo, expr_ref& dd);

    // epoch day number of a date term: a numeral for ground terms, the
    // shared internal term (date.epoch! d) otherwise
    expr_ref mk_epoch(expr* d);

    // formulas asserting calendar validity of the components (y, mo, d)
    void mk_valid_spec(expr* y, expr* mo, expr* d, expr_ref_vector& fmls);

    // formulas linking the selectors (ty, tm, td) of a date.mk term to its
    // arguments (y, mo, d): if the argument triple is valid the selectors
    // agree with it, otherwise the term is unconstrained (fresh valid date)
    void mk_mk_spec(expr* y, expr* mo, expr* d, expr* ty, expr* tm, expr* td, expr_ref_vector& fmls);

    // all defining formulas for the date term t: calendar validity of its
    // selectors, the definition of its epoch term, and, for
    // date.mk/date.add/date.sub applications, the arithmetic definition
    // of the operation
    void mk_term_spec(expr* t, expr_ref_vector& fmls);

    // arithmetic definition of a comparison between the date terms a and b,
    // as a comparison of epoch day numbers
    expr_ref mk_cmp_spec(decl_kind k, expr* a, expr* b);

    // equivalent definition of the comparison as a lexicographic comparison
    // of the (year, month, day) components. Asserting both definitions is
    // redundant but lets the arithmetic solver pick the cheaper route:
    // the epoch form composes with date.add/date.sub, the lexicographic
    // form makes order-theoretic facts (e.g. antisymmetry) shallow.
    expr_ref mk_cmp_lex_spec(decl_kind k, expr* a, expr* b);
};
