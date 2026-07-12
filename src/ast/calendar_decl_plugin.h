/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    calendar_decl_plugin.h

Abstract:

    Theory of calendar dates over the proleptic Gregorian calendar.

    All operators work on integers.  A *date* is either given by its
    fields (year, month, day) or by its *epoch day number*: the number
    of days since 1970-01-01 (day 0).  Years follow astronomical
    numbering (year 0 = 1 BC, year -1 = 2 BC, ...), and the Gregorian
    leap rules are extrapolated to all integers (proleptic calendar).

    Operators:

      (date.is-leap-year  y)      Int -> Bool
          true iff y is a Gregorian leap year:
          (y mod 4 = 0 and y mod 100 != 0) or y mod 400 = 0.

      (date.days-in-month y m)    Int Int -> Int
          number of days in month m of year y (31/30/29/28);
          0 when m is not in [1, 12].

      (date.valid y m d)          Int Int Int -> Bool
          true iff (y, m, d) denotes a calendar date:
          1 <= m <= 12 and 1 <= d <= (date.days-in-month y m).

      (date.to-epoch y m d)       Int Int Int -> Int
          epoch day number of the date (y, m, d).  On valid dates this
          is the days-since-1970-01-01 count; on arbitrary integers it
          is the total function computed by the days-from-civil
          algorithm (see calendar_rewriter.cpp).

      (date.year  n)              Int -> Int
      (date.month n)              Int -> Int
      (date.day   n)              Int -> Int
          fields of the date whose epoch day number is n.  For every
          integer n the triple (year, month, day) is the unique valid
          date with (date.to-epoch (date.year n) (date.month n)
          (date.day n)) = n.

      (date.day-of-week n)        Int -> Int
          day of week of epoch day n, in [0, 6] with 0 = Sunday,
          1 = Monday, ..., 6 = Saturday.  (Day 0, 1970-01-01, was a
          Thursday, so (date.day-of-week 0) = 4.)

    The semantics of every operator is *defined* by its expansion into
    integer arithmetic (linear arithmetic with div/mod by numeric
    constants) implemented in ast/rewriter/calendar_rewriter.cpp.  The
    expansion introduces no fresh symbols, so it is a definitional and
    hence sound (and complete) reduction; the target fragment is
    decidable.

Author:

    Claude (Anthropic) 2026-07-12

--*/
#pragma once

#include "ast/ast.h"

enum calendar_op_kind {
    OP_DATE_IS_LEAP_YEAR,
    OP_DATE_DAYS_IN_MONTH,
    OP_DATE_VALID,
    OP_DATE_TO_EPOCH,
    OP_DATE_YEAR,
    OP_DATE_MONTH,
    OP_DATE_DAY,
    OP_DATE_DAY_OF_WEEK,
    LAST_CALENDAR_OP
};

class calendar_decl_plugin : public decl_plugin {
public:
    decl_plugin * mk_fresh() override {
        return alloc(calendar_decl_plugin);
    }

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;

    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override { return nullptr; }
};

class calendar_util {
    ast_manager&        m;
    mutable family_id   m_fid;
public:
    calendar_util(ast_manager& m): m(m), m_fid(null_family_id) {}

    family_id get_family_id() const {
        if (null_family_id == m_fid)
            m_fid = m.mk_family_id("calendar");
        return m_fid;
    }

    bool is_calendar_op(expr const* e) const { return is_app(e) && to_app(e)->get_family_id() == get_family_id(); }
    bool is_calendar_op(func_decl const* f) const { return f->get_family_id() == get_family_id(); }

    bool is_leap_year(expr const* e) const { return is_app_of(e, get_family_id(), OP_DATE_IS_LEAP_YEAR); }
    bool is_days_in_month(expr const* e) const { return is_app_of(e, get_family_id(), OP_DATE_DAYS_IN_MONTH); }
    bool is_valid(expr const* e) const { return is_app_of(e, get_family_id(), OP_DATE_VALID); }
    bool is_to_epoch(expr const* e) const { return is_app_of(e, get_family_id(), OP_DATE_TO_EPOCH); }
    bool is_year(expr const* e) const { return is_app_of(e, get_family_id(), OP_DATE_YEAR); }
    bool is_month(expr const* e) const { return is_app_of(e, get_family_id(), OP_DATE_MONTH); }
    bool is_day(expr const* e) const { return is_app_of(e, get_family_id(), OP_DATE_DAY); }
    bool is_day_of_week(expr const* e) const { return is_app_of(e, get_family_id(), OP_DATE_DAY_OF_WEEK); }

    app * mk_is_leap_year(expr* y) { return m.mk_app(get_family_id(), OP_DATE_IS_LEAP_YEAR, y); }
    app * mk_days_in_month(expr* y, expr* mo) { return m.mk_app(get_family_id(), OP_DATE_DAYS_IN_MONTH, y, mo); }
    app * mk_valid(expr* y, expr* mo, expr* d) { return m.mk_app(get_family_id(), OP_DATE_VALID, y, mo, d); }
    app * mk_to_epoch(expr* y, expr* mo, expr* d) { return m.mk_app(get_family_id(), OP_DATE_TO_EPOCH, y, mo, d); }
    app * mk_year(expr* n) { return m.mk_app(get_family_id(), OP_DATE_YEAR, n); }
    app * mk_month(expr* n) { return m.mk_app(get_family_id(), OP_DATE_MONTH, n); }
    app * mk_day(expr* n) { return m.mk_app(get_family_id(), OP_DATE_DAY, n); }
    app * mk_day_of_week(expr* n) { return m.mk_app(get_family_id(), OP_DATE_DAY_OF_WEEK, n); }
};
