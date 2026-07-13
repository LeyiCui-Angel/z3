/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Declaration plugin for the theory of calendar dates.

    A Date value denotes a day of the proleptic Gregorian calendar
    (astronomical year numbering, unbounded years). Every Date is in
    bijection with an integer epoch day number, where day 0 is
    1970-01-01. The bijection is realized by the civil-from-days and
    days-from-civil algorithms of Howard Hinnant, which only use
    integer division by positive constants.

    Semantic conventions implemented here and by the theory solvers:

    - (date.mk y m d) is total at the sorting level, but semantically
      strict: it denotes a date only when the arguments form a valid
      civil date, i.e. 1 <= m <= 12 and 1 <= d <= days-in-month(y, m).
      The theory solvers assert these validity constraints for every
      occurrence of date.mk, so constraints that force an application
      of date.mk to out-of-range components (e.g. (date.mk 2020 2 30))
      are unsatisfiable. There is no normalization: February 30th is
      not a date.

    - date.year/date.month/date.day return exactly the components the
      date was constructed from.

    - (date.add d py pm pd) adds 12*py + pm months in a single step,
      clamps the day-of-month to the length of the target month
      (the java.time / relativedelta convention: Jan 31 plus one month
      is Feb 28 or 29), and finally adds pd days exactly.

    - (date.sub d py pm pd) = (date.add d (- py) (- pm) (- pd)).

    - date.lt/le/gt/ge compare dates chronologically, i.e., by epoch
      day number.

Author:

    Z3 date theory extension 2026-07-05

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
    // internal: injection of Date into its epoch day number.
    // not exposed through the SMT-LIB front-end.
    OP_DATE_EPOCH
};

class date_decl_plugin : public decl_plugin {
    sort* m_date { nullptr };

    void set_manager(ast_manager* m, family_id id) override;

    func_decl* mk_decl(decl_kind k, char const* name, unsigned arity,
                       sort* const* domain, sort* range);

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

/**
   \brief Utilities for constructing and decomposing date terms, and for
   evaluating the calendar functions over arbitrary precision integers.
*/
class date_util {
    ast_manager&      m;
    family_id         m_fid;
    date_decl_plugin* m_plugin;
    arith_util        m_arith;

    // building blocks for the symbolic encodings
    expr_ref mk_num(int n);
    expr_ref mk_num(rational const& r);
    expr_ref mk_idiv(expr* x, int c);
    expr_ref mk_imod(expr* x, int c);
    // day-of-year offset of the first day of month mo (Hinnant's
    // (153*mp+2)/5 table folded into an ite table over mo in [1,12])
    expr_ref mk_month_offset(expr* mo);
    // 0/1 indicator of mo <= 2, the only ite feeding the shifted year
    // and month offset of days-from-civil
    expr_ref mk_jan_feb_flag(expr* mo);

public:
    date_util(ast_manager& m):
        m(m),
        m_fid(m.mk_family_id("date")),
        m_plugin(static_cast<date_decl_plugin*>(m.get_plugin(m_fid))),
        m_arith(m) {}

    ast_manager& get_manager() const { return m; }
    family_id get_family_id() const { return m_fid; }
    date_decl_plugin& plugin() const { return *m_plugin; }
    arith_util& arith() const { return const_cast<date_util*>(this)->m_arith; }

    sort* mk_date_sort() const { return m_plugin->date_sort(); }
    bool is_date(sort* s) const { return is_sort_of(s, m_fid, DATE_SORT); }
    bool is_date(expr* e) const { return is_date(e->get_sort()); }

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

    app* mk_mk(expr* y, expr* mo, expr* d);
    app* mk_epoch(expr* d);
    app* mk_year(expr* d);
    app* mk_month(expr* d);
    app* mk_day(expr* d);

    /**
       \brief Negation of an Int term; numerals are negated in place so
       that offset fast paths can recognize them.
    */
    expr_ref mk_ineg(expr* e);

    /**
       \brief Date value from an epoch day number: (date.mk y m d) with
       the valid civil components of that day as numeral arguments.
    */
    app* mk_date_value(rational const& epoch);

    /**
       \brief Recognize (date.mk y m d) with numeral arguments; returns the
       components, which need not form a valid date.
    */
    bool is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d) const;

    /**
       \brief Recognize a canonical date value: (date.mk y m d) with numeral
       arguments denoting a valid calendar date. Returns its epoch day.
    */
    bool is_date_value(expr const* e, rational& epoch) const;
    bool is_date_value(expr const* e) const { rational z; return is_date_value(e, z); }

    // ------------------------------------------------------------------
    // concrete calendar arithmetic (arbitrary precision)

    static bool is_leap_year(rational const& y);
    static rational days_in_month(rational const& y, rational const& mo);
    // strict constructor semantics: 1 <= mo <= 12 and 1 <= d <= days_in_month
    static bool is_valid_civil(rational const& y, rational const& mo, rational const& d);
    // epoch of a valid civil triple (mo in [1,12], d unrestricted offset)
    static rational days_from_civil(rational const& y, rational const& mo, rational const& d);
    static void civil_of_epoch(rational const& z, rational& y, rational& mo, rational& d);
    // date.add semantics on epoch days
    static rational add_to_epoch(rational const& z, rational const& py, rational const& pm, rational const& pd);

    // ------------------------------------------------------------------
    // symbolic encodings of the calendar functions over Int terms.
    // All use only linear arithmetic, ite, and div/mod by small
    // constants (4, 100, 400 on the shifted year; 12 on month totals).
    // The theory solvers use a purely *forward* (relational) encoding:
    // the components of a date are represented by its selector terms,
    // constrained to a valid civil triple whose days-from-civil image is
    // the date's epoch. The inverse civil-of-epoch direction is never
    // encoded symbolically -- recovering components from an epoch is
    // left to the integer solver's search over the (tightly bounded)
    // component variables, which is far cheaper than the div towers by
    // 146097/36524/1460 that a symbolic inverse requires.

    // number of days in month mo of year y, for mo in [1,12]
    expr_ref mk_days_in_month(expr* y, expr* mo);
    // epoch of the civil triple (y, mo, d) for mo in [1,12]
    expr_ref mk_days_from_civil(expr* y, expr* mo, expr* d);
    // absolute month count 12*y + mo of a civil pair; month arithmetic
    // is linear on this view, and mo in [1,12] makes the decomposition
    // unique, so the solvers never need div/mod by 12
    expr_ref mk_month_total(expr* y, expr* mo);
    // dd clamped to the length of month mo of year y (end-of-month rule)
    expr_ref mk_clamped_day(expr* dd, expr* y, expr* mo);
    // tautological bound cuts over the ite terms of the civil encoding
    // of (y, mo): 0 <= jan-feb-flag <= 1 and 28 <= days-in-month <= 31.
    // Redundant for the Boolean search, but an ite variable has no LP
    // row until its condition is decided; without the cuts the epoch of
    // a date is completely decoupled from its components in the LP
    // relaxation and the integer solver's model search is blind.
    void mk_civil_cuts(expr* y, expr* mo, expr_ref_vector& cuts);
    // lo/hi bounds (in days) on epoch(date.add b py pm 0) - epoch(b)
    // for a month shift of s = 12*py + pm months, end-of-month clamp
    // included. Valid for every valid base date and every integer s.
    static void month_span_bounds(rational const& s, rational& lo, rational& hi);
    // true if py and pm are numerals denoting a zero month shift, so
    // date.add reduces to a pure day shift on epochs
    bool is_zero_month_shift(expr* py, expr* pm) const;
    // true if e is the numeral zero
    bool is_zero(expr* e) const;
};
