/*++
Copyright (c) 2026 Theoria contributors

Module Name:

    calendar_decl_plugin.h

Abstract:

    Declaration plugin for a theory of calendar dates over the
    proleptic Gregorian calendar.

    The theory introduces a family of interpreted functions over the
    integers.  A calendar date is represented either by the triple
    (year, month, day) or by its "epoch day" number: the number of
    days elapsed since 1970-01-01 (negative for earlier dates).  The
    calendar is the proleptic Gregorian calendar, i.e. the Gregorian
    leap-year rules extended indefinitely in both directions, with
    astronomical year numbering (year 0 exists and is a leap year).

    Operators (all integer arguments):

      (date.to-epoch y m d)     Int Int Int -> Int
          Epoch day number of the date y-m-d.  For valid dates
          (see date.valid) this is the calendar date's day number.
          The function is made total by the defining arithmetic
          expression; out-of-range m/d extend it linearly in d.

      (date.year e)             Int -> Int
      (date.month e)            Int -> Int
      (date.day e)              Int -> Int
          The unique valid date (y, m, d) whose epoch day number is e.

      (date.day-of-week e)      Int -> Int
          Day of week of epoch day e; 0 = Sunday, ..., 6 = Saturday.

      (date.leap-year y)        Int -> Bool
          Gregorian leap-year predicate.

      (date.days-in-month y m)  Int Int -> Int
          Number of days in month m of year y (for m in [1,12]).

      (date.valid y m d)        Int Int Int -> Bool
          1 <= m <= 12 and 1 <= d <= (date.days-in-month y m).

    The theory is implemented as a sound definitional extension: every
    operator is eliminated by calendar_rewriter, which replaces it with
    an equivalent linear-integer-arithmetic term (using div/mod by
    numeric constants and if-then-else).  No fresh symbols and no
    axioms are introduced, so satisfiability is preserved exactly.

Author:

    Claude (Theoria) 2026-07-12

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"

enum calendar_op_kind {
    OP_DATE_TO_EPOCH,
    OP_DATE_YEAR,
    OP_DATE_MONTH,
    OP_DATE_DAY,
    OP_DATE_DAY_OF_WEEK,
    OP_DATE_LEAP_YEAR,
    OP_DATE_DAYS_IN_MONTH,
    OP_DATE_VALID,
    LAST_CALENDAR_OP
};

class calendar_decl_plugin : public decl_plugin {
    symbol m_to_epoch;
    symbol m_year;
    symbol m_month;
    symbol m_day;
    symbol m_day_of_week;
    symbol m_leap_year;
    symbol m_days_in_month;
    symbol m_valid;
public:
    calendar_decl_plugin();

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

    family_id fid() const {
        if (null_family_id == m_fid)
            m_fid = m.get_family_id("calendar");
        return m_fid;
    }
public:
    calendar_util(ast_manager& m): m(m), m_fid(null_family_id) {}

    family_id get_family_id() const { return fid(); }

    bool is_calendar(func_decl* f) const { return f->get_family_id() == fid(); }
    bool is_calendar(expr* e) const { return is_app(e) && is_calendar(to_app(e)->get_decl()); }

    bool is_to_epoch(expr const * e) const { return is_app_of(e, fid(), OP_DATE_TO_EPOCH); }
    bool is_year(expr const * e) const { return is_app_of(e, fid(), OP_DATE_YEAR); }
    bool is_month(expr const * e) const { return is_app_of(e, fid(), OP_DATE_MONTH); }
    bool is_day(expr const * e) const { return is_app_of(e, fid(), OP_DATE_DAY); }
    bool is_day_of_week(expr const * e) const { return is_app_of(e, fid(), OP_DATE_DAY_OF_WEEK); }
    bool is_leap_year(expr const * e) const { return is_app_of(e, fid(), OP_DATE_LEAP_YEAR); }
    bool is_days_in_month(expr const * e) const { return is_app_of(e, fid(), OP_DATE_DAYS_IN_MONTH); }
    bool is_valid(expr const * e) const { return is_app_of(e, fid(), OP_DATE_VALID); }

    app * mk_to_epoch(expr* y, expr* mo, expr* d) { expr* args[3] = { y, mo, d }; return m.mk_app(fid(), OP_DATE_TO_EPOCH, 3, args); }
    app * mk_year(expr* e) { return m.mk_app(fid(), OP_DATE_YEAR, e); }
    app * mk_month(expr* e) { return m.mk_app(fid(), OP_DATE_MONTH, e); }
    app * mk_day(expr* e) { return m.mk_app(fid(), OP_DATE_DAY, e); }
    app * mk_day_of_week(expr* e) { return m.mk_app(fid(), OP_DATE_DAY_OF_WEEK, e); }
    app * mk_leap_year(expr* y) { return m.mk_app(fid(), OP_DATE_LEAP_YEAR, y); }
    app * mk_days_in_month(expr* y, expr* mo) { return m.mk_app(fid(), OP_DATE_DAYS_IN_MONTH, y, mo); }
    app * mk_valid(expr* y, expr* mo, expr* d) { expr* args[3] = { y, mo, d }; return m.mk_app(fid(), OP_DATE_VALID, 3, args); }
};
