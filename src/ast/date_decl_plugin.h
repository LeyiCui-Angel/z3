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

    - (date.mk y m d) is total. The month is normalized first:
      overflow and underflow of the month carry into the year
      (mo = 12*y + m - 1 total months). The day is then interpreted
      as an offset from day 1 of the resolved month, so out-of-range
      days spill over into adjacent months (mktime convention).
      Examples: (date.mk 2000 2 30) = 2000-03-01,
                (date.mk 2000 13 1) = 2001-01-01,
                (date.mk 2000 1 0)  = 1999-12-31.

    - date.year/date.month/date.day return the components of the
      normalized date.

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
    struct civil_expr {
        expr_ref y, m, d;
        civil_expr(ast_manager& mgr): y(mgr), m(mgr), d(mgr) {}
    };
    void mk_civil_of_epoch(expr* z, civil_expr& c);
    expr_ref mk_days_from_civil(expr* y, expr* mo, expr* d);

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

    /**
       \brief Date value from an epoch day number: (date.mk y m d) with
       normalized numeral arguments.
    */
    app* mk_date_value(rational const& epoch);

    /**
       \brief Recognize (date.mk y m d) with numeral arguments; returns the
       (unnormalized) components.
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
    // total constructor semantics: month overflow first, then day offset
    static rational epoch_of_ymd(rational const& y, rational const& mo, rational const& d);
    // epoch of a valid civil triple (mo in [1,12], d unrestricted offset)
    static rational days_from_civil(rational const& y, rational const& mo, rational const& d);
    static void civil_of_epoch(rational const& z, rational& y, rational& mo, rational& d);
    // date.add semantics on epoch days
    static rational add_to_epoch(rational const& z, rational const& py, rational const& pm, rational const& pd);

    // ------------------------------------------------------------------
    // symbolic encodings of the calendar functions over Int terms.
    // All use only linear arithmetic, ite, and div/mod by constants.

    // epoch of (date.mk y mo d) - the total constructor
    expr_ref mk_epoch_of_ymd(expr* y, expr* mo, expr* d);
    // components of a date given by its epoch day
    expr_ref mk_year_of_epoch(expr* z);
    expr_ref mk_month_of_epoch(expr* z);
    expr_ref mk_day_of_epoch(expr* z);
    // epoch of (date.add d py pm pd) given z = epoch of d
    expr_ref mk_epoch_of_add(expr* z, expr* py, expr* pm, expr* pd);
    // days-from-civil over the components of z: equal to z for every z.
    // Providing this identity as an axiom lets the solvers derive
    // injectivity of the component map by congruence.
    expr_ref mk_civil_roundtrip(expr* z);
};
