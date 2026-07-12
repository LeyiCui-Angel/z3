/*++
Copyright (c) 2026 Theoria contributors

Module Name:

    calendar_decl_plugin.cpp

Abstract:

    Declaration plugin for the theory of calendar dates.
    See calendar_decl_plugin.h for the semantics of the operators.

Author:

    Claude (Theoria) 2026-07-12

--*/

#include "ast/calendar_decl_plugin.h"
#include "ast/arith_decl_plugin.h"

calendar_decl_plugin::calendar_decl_plugin():
    m_to_epoch("date.to-epoch"),
    m_year("date.year"),
    m_month("date.month"),
    m_day("date.day"),
    m_day_of_week("date.day-of-week"),
    m_leap_year("date.leap-year"),
    m_days_in_month("date.days-in-month"),
    m_valid("date.valid")
{}

func_decl * calendar_decl_plugin::mk_func_decl(
    decl_kind k, unsigned num_parameters, parameter const * parameters,
    unsigned arity, sort * const * domain, sort * range)
{
    ast_manager& m = *m_manager;
    if (num_parameters != 0) {
        m.raise_exception("calendar operators do not take parameters");
        return nullptr;
    }

    sort * int_sort = m.mk_sort(m.mk_family_id("arith"), INT_SORT);
    sort * bool_sort = m.mk_bool_sort();

    unsigned expected_arity;
    symbol name;
    sort * rng;
    switch (k) {
    case OP_DATE_TO_EPOCH:      expected_arity = 3; name = m_to_epoch;      rng = int_sort;  break;
    case OP_DATE_YEAR:          expected_arity = 1; name = m_year;          rng = int_sort;  break;
    case OP_DATE_MONTH:         expected_arity = 1; name = m_month;         rng = int_sort;  break;
    case OP_DATE_DAY:           expected_arity = 1; name = m_day;           rng = int_sort;  break;
    case OP_DATE_DAY_OF_WEEK:   expected_arity = 1; name = m_day_of_week;   rng = int_sort;  break;
    case OP_DATE_LEAP_YEAR:     expected_arity = 1; name = m_leap_year;     rng = bool_sort; break;
    case OP_DATE_DAYS_IN_MONTH: expected_arity = 2; name = m_days_in_month; rng = int_sort;  break;
    case OP_DATE_VALID:         expected_arity = 3; name = m_valid;         rng = bool_sort; break;
    default:
        m.raise_exception("unknown calendar operator");
        return nullptr;
    }

    if (arity != expected_arity) {
        m.raise_exception("wrong number of arguments to calendar operator");
        return nullptr;
    }
    for (unsigned i = 0; i < arity; ++i) {
        if (domain[i] != int_sort) {
            m.raise_exception("calendar operators expect integer arguments");
            return nullptr;
        }
    }
    if (range && range != rng) {
        m.raise_exception("calendar operator applied with wrong range sort");
        return nullptr;
    }

    func_decl_info info(m_family_id, k);
    return m.mk_func_decl(name, arity, domain, rng, info);
}

void calendar_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null || logic == "ALL") {
        op_names.push_back(builtin_name(m_to_epoch.str(), OP_DATE_TO_EPOCH));
        op_names.push_back(builtin_name(m_year.str(), OP_DATE_YEAR));
        op_names.push_back(builtin_name(m_month.str(), OP_DATE_MONTH));
        op_names.push_back(builtin_name(m_day.str(), OP_DATE_DAY));
        op_names.push_back(builtin_name(m_day_of_week.str(), OP_DATE_DAY_OF_WEEK));
        op_names.push_back(builtin_name(m_leap_year.str(), OP_DATE_LEAP_YEAR));
        op_names.push_back(builtin_name(m_days_in_month.str(), OP_DATE_DAYS_IN_MONTH));
        op_names.push_back(builtin_name(m_valid.str(), OP_DATE_VALID));
    }
}
