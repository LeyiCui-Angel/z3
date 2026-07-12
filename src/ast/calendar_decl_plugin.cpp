/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    calendar_decl_plugin.cpp

Abstract:

    Theory of calendar dates over the proleptic Gregorian calendar.
    See calendar_decl_plugin.h for the semantics of the operators.

Author:

    Claude (Anthropic) 2026-07-12

--*/

#include <sstream>
#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/calendar_decl_plugin.h"

func_decl * calendar_decl_plugin::mk_func_decl(
    decl_kind k, unsigned num_parameters, parameter const * parameters,
    unsigned arity, sort * const * domain, sort * range)
{
    if (num_parameters != 0) {
        m_manager->raise_exception("calendar operators do not accept parameters");
        return nullptr;
    }
    arith_util au(*m_manager);
    sort * int_s  = au.mk_int();
    sort * bool_s = m_manager->mk_bool_sort();
    char const * name = nullptr;
    unsigned expected_arity = 0;
    sort * rng = nullptr;
    switch (k) {
    case OP_DATE_IS_LEAP_YEAR:  name = "date.is-leap-year";  expected_arity = 1; rng = bool_s; break;
    case OP_DATE_DAYS_IN_MONTH: name = "date.days-in-month"; expected_arity = 2; rng = int_s;  break;
    case OP_DATE_VALID:         name = "date.valid";         expected_arity = 3; rng = bool_s; break;
    case OP_DATE_TO_EPOCH:      name = "date.to-epoch";      expected_arity = 3; rng = int_s;  break;
    case OP_DATE_YEAR:          name = "date.year";          expected_arity = 1; rng = int_s;  break;
    case OP_DATE_MONTH:         name = "date.month";         expected_arity = 1; rng = int_s;  break;
    case OP_DATE_DAY:           name = "date.day";           expected_arity = 1; rng = int_s;  break;
    case OP_DATE_DAY_OF_WEEK:   name = "date.day-of-week";   expected_arity = 1; rng = int_s;  break;
    default:
        m_manager->raise_exception("unknown calendar operator");
        return nullptr;
    }
    if (arity != expected_arity) {
        std::stringstream strm;
        strm << name << " expects " << expected_arity << " argument(s), but " << arity << " were provided";
        m_manager->raise_exception(strm.str());
        return nullptr;
    }
    for (unsigned i = 0; i < arity; ++i) {
        if (domain[i] != int_s) {
            std::stringstream strm;
            strm << "arguments of " << name << " must have sort Int";
            m_manager->raise_exception(strm.str());
            return nullptr;
        }
    }
    if (range && range != rng) {
        std::stringstream strm;
        strm << "invalid range sort for " << name;
        m_manager->raise_exception(strm.str());
        return nullptr;
    }
    return m_manager->mk_func_decl(symbol(name), arity, domain, rng, func_decl_info(m_family_id, k));
}

void calendar_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null || logic == "ALL") {
        op_names.push_back(builtin_name("date.is-leap-year",  OP_DATE_IS_LEAP_YEAR));
        op_names.push_back(builtin_name("date.days-in-month", OP_DATE_DAYS_IN_MONTH));
        op_names.push_back(builtin_name("date.valid",         OP_DATE_VALID));
        op_names.push_back(builtin_name("date.to-epoch",      OP_DATE_TO_EPOCH));
        op_names.push_back(builtin_name("date.year",          OP_DATE_YEAR));
        op_names.push_back(builtin_name("date.month",         OP_DATE_MONTH));
        op_names.push_back(builtin_name("date.day",           OP_DATE_DAY));
        op_names.push_back(builtin_name("date.day-of-week",   OP_DATE_DAY_OF_WEEK));
    }
}
