/*++
Copyright (c) 2026 Theoria

Module Name:

    date_decl_plugin.h

Abstract:

    Declaration plugin for the theory of calendar dates.

    The theory introduces the sort Date, whose intended interpretation is
    the set of days of the proleptic Gregorian calendar. The carrier is
    isomorphic to the integers via the bijection

        date.to_days   : Date -> Int   (days since the epoch 1970-01-01)
        date.from_days : Int  -> Date

    All other operations are definitional over this bijection:

        (date.mk y m d)        the date with year y, month m, day d.
                               Defined for all integer inputs by the
                               days-from-civil formula (see date_rewriter);
                               it agrees with the calendar on valid triples
                               (guard with date.valid to restrict to those).
        (date.year t)          year of t (proleptic Gregorian, may be <= 0)
        (date.month t)         month of t, in [1,12]
        (date.day t)           day-of-month of t, in [1,31]
        (date.add_days t n)    the date n days after t
        (date.sub t1 t2)       number of days from t2 to t1
        (date.dow t)           ISO-8601 day of week: 1 = Monday ... 7 = Sunday
        (date.lt t1 t2)        t1 is strictly before t2
        (date.le t1 t2)        t1 is before or equal to t2
        (date.valid y m d)     y/m/d is a valid proleptic Gregorian date
        (date.leap_year y)     y is a leap year (Gregorian rule)

    The theory is decided soundly and completely (for the supported
    fragment) by reduction to linear integer arithmetic with integer
    division/modulus by constants; see ast/rewriter/date_rewriter.h.

Author:

    Claude (Theoria date theory) 2026-07-07

--*/
#pragma once

#include "ast/ast.h"

enum date_sort_kind {
    DATE_SORT
};

enum date_op_kind {
    OP_DATE_MK,          // Int Int Int -> Date
    OP_DATE_YEAR,        // Date -> Int
    OP_DATE_MONTH,       // Date -> Int
    OP_DATE_DAY,         // Date -> Int
    OP_DATE_TO_DAYS,     // Date -> Int
    OP_DATE_FROM_DAYS,   // Int -> Date
    OP_DATE_ADD_DAYS,    // Date Int -> Date
    OP_DATE_SUB,         // Date Date -> Int
    OP_DATE_DOW,         // Date -> Int
    OP_DATE_LT,          // Date Date -> Bool
    OP_DATE_LE,          // Date Date -> Bool
    OP_DATE_VALID,       // Int Int Int -> Bool
    OP_DATE_LEAP_YEAR,   // Int -> Bool
    LAST_DATE_OP
};

class date_decl_plugin : public decl_plugin {
    sort* m_date { nullptr };
    sort* m_int { nullptr };

    void set_manager(ast_manager * m, family_id id) override;

    func_decl * mk_op(char const* name, decl_kind k, unsigned arity, sort * const * domain, sort * range);

public:
    date_decl_plugin() = default;

    ~date_decl_plugin() override;

    void finalize() override {}

    decl_plugin * mk_fresh() override { return alloc(date_decl_plugin); }

    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;

    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    bool is_value(app * e) const override;

    bool is_unique_value(app * e) const override;

    expr * get_some_value(sort * s) override;

    sort * date_sort() const { return m_date; }
};

class date_util {
    ast_manager & m;
    date_decl_plugin * m_plugin;
    family_id     m_fid;

public:
    date_util(ast_manager & m);

    ast_manager & get_manager() const { return m; }
    family_id get_family_id() const { return m_fid; }
    date_decl_plugin & plugin() const { return *m_plugin; }

    sort * mk_date_sort() const { return m_plugin->date_sort(); }
    bool is_date_sort(sort * s) const { return is_sort_of(s, m_fid, DATE_SORT); }
    bool is_date(expr const * e) const { return is_date_sort(e->get_sort()); }

    // true if s is the Date sort or a composite sort (array, seq, ...) that
    // mentions Date among its parameters.
    bool sort_contains_date(sort * s) const;

    app * mk_mk_date(expr * y, expr * mo, expr * d) {
        expr * args[3] = { y, mo, d };
        return m.mk_app(m_fid, OP_DATE_MK, 3, args);
    }
    app * mk_to_days(expr * t) { return m.mk_app(m_fid, OP_DATE_TO_DAYS, 1, &t); }
    app * mk_from_days(expr * n) { return m.mk_app(m_fid, OP_DATE_FROM_DAYS, 1, &n); }
    app * mk_year(expr * t) { return m.mk_app(m_fid, OP_DATE_YEAR, 1, &t); }
    app * mk_month(expr * t) { return m.mk_app(m_fid, OP_DATE_MONTH, 1, &t); }
    app * mk_day(expr * t) { return m.mk_app(m_fid, OP_DATE_DAY, 1, &t); }

    bool is_from_days(expr const * e) const { return is_app_of(e, m_fid, OP_DATE_FROM_DAYS); }
    bool is_from_days(expr const * e, expr *& arg) const {
        if (!is_from_days(e)) return false;
        arg = to_app(e)->get_arg(0);
        return true;
    }
    bool is_to_days(expr const * e) const { return is_app_of(e, m_fid, OP_DATE_TO_DAYS); }
    bool is_mk_date(expr const * e) const { return is_app_of(e, m_fid, OP_DATE_MK); }
};
