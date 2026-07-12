/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    calendar_rewriter.cpp

Abstract:

    Rewriting (definitional expansion) of calendar date operators into
    integer arithmetic.

    Every calendar operator is expanded into a term built from integer
    addition, multiplication by constants, div/mod by positive numeric
    constants, if-then-else and boolean connectives.  No fresh symbols
    are introduced, so the expansion is definitional: it is sound in
    any polarity and under quantifiers, and it lands in a decidable
    fragment (linear integer arithmetic with div/mod by constants).

    The field <-> epoch-day conversions use Howard Hinnant's
    days_from_civil / civil_from_days algorithms
    (https://howardhinnant.github.io/date_algorithms.html), which are
    exact on the proleptic Gregorian calendar for all integer years.
    The C++ formulation relies on truncated division on non-negative
    operands; here all divisors are positive constants, and SMT-LIB
    integer div/mod are Euclidean, which coincides with floor division
    for positive divisors, so the shift-based tricks of the original
    (moving the era origin) are unnecessary: era = y div 400 and
    year-of-era = y mod 400 are already correct for negative years.

Author:

    Claude (Anthropic) 2026-07-12

--*/

#include "ast/ast_util.h"
#include "ast/rewriter/calendar_rewriter.h"

// (y mod 4 = 0 and y mod 100 != 0) or y mod 400 = 0
expr_ref calendar_rewriter::mk_is_leap_year(expr* y) {
    expr* zero = mk_num(0);
    return expr_ref(
        m.mk_or(
            m.mk_and(
                m.mk_eq(mk_mod(y, 4), zero),
                m.mk_not(m.mk_eq(mk_mod(y, 100), zero))),
            m.mk_eq(mk_mod(y, 400), zero)),
        m);
}

// 31 for months {1,3,5,7,8,10,12}, 30 for {4,6,9,11},
// 29/28 for February depending on leap year, 0 outside [1,12].
expr_ref calendar_rewriter::mk_days_in_month(expr* y, expr* mo) {
    expr* is31[7] = {
        m.mk_eq(mo, mk_num(1)),  m.mk_eq(mo, mk_num(3)),  m.mk_eq(mo, mk_num(5)),
        m.mk_eq(mo, mk_num(7)),  m.mk_eq(mo, mk_num(8)),  m.mk_eq(mo, mk_num(10)),
        m.mk_eq(mo, mk_num(12))
    };
    expr* is30[4] = {
        m.mk_eq(mo, mk_num(4)),  m.mk_eq(mo, mk_num(6)),
        m.mk_eq(mo, mk_num(9)),  m.mk_eq(mo, mk_num(11))
    };
    expr* feb = m.mk_ite(m_util.mk_is_leap_year(y), mk_num(29), mk_num(28));
    return expr_ref(
        m.mk_ite(::mk_or(m, 7, is31), mk_num(31),
            m.mk_ite(::mk_or(m, 4, is30), mk_num(30),
                m.mk_ite(m.mk_eq(mo, mk_num(2)), feb, mk_num(0)))),
        m);
}

// 1 <= mo <= 12 and 1 <= d <= days-in-month(y, mo)
expr_ref calendar_rewriter::mk_valid(expr* y, expr* mo, expr* d) {
    expr* one = mk_num(1);
    expr* conjs[4] = {
        m_arith.mk_le(one, mo),
        m_arith.mk_le(mo, mk_num(12)),
        m_arith.mk_le(one, d),
        m_arith.mk_le(d, m_util.mk_days_in_month(y, mo))
    };
    return expr_ref(::mk_and(m, 4, conjs), m);
}

// days_from_civil: epoch day number of (y, mo, d), day 0 = 1970-01-01.
expr_ref calendar_rewriter::mk_to_epoch(expr* y, expr* mo, expr* d) {
    // yy  = if mo <= 2 then y - 1 else y      (shifted year: year starts in March)
    // era = yy div 400,  yoe = yy mod 400                                 in [0, 399]
    // mp  = (mo + 9) mod 12                   (March = 0, ..., February = 11)
    // doy = (153*mp + 2) div 5 + d - 1                                    in [0, 365]
    // doe = yoe*365 + yoe div 4 - yoe div 100 + doy                       in [0, 146096]
    // result = era*146097 + doe - 719468      (719468 = days from 0000-03-01 to 1970-01-01)
    expr* yy  = m.mk_ite(m_arith.mk_le(mo, mk_num(2)),
                         m_arith.mk_sub(y, mk_num(1)), y);
    expr* era = mk_div(yy, 400);
    expr* yoe = mk_mod(yy, 400);
    expr* mp  = mk_mod(m_arith.mk_add(mo, mk_num(9)), 12);
    expr* doy = m_arith.mk_add(
        mk_div(m_arith.mk_add(m_arith.mk_mul(mk_num(153), mp), mk_num(2)), 5),
        d, mk_num(-1));
    expr* doe_args[4] = {
        m_arith.mk_mul(mk_num(365), yoe),
        mk_div(yoe, 4),
        m_arith.mk_mul(mk_num(-1), mk_div(yoe, 100)),
        doy
    };
    expr* doe = m_arith.mk_add(4, doe_args);
    return expr_ref(
        m_arith.mk_add(m_arith.mk_mul(mk_num(146097), era), doe, mk_num(-719468)),
        m);
}

// civil_from_days: fields (year, month, day) of epoch day n.
void calendar_rewriter::mk_civil_parts(expr* n, expr_ref& year, expr_ref& month, expr_ref& day) {
    // z   = n + 719468
    // era = z div 146097,  doe = z mod 146097                             in [0, 146096]
    // yoe = (doe - doe div 1460 + doe div 36524 - doe div 146096) div 365 in [0, 399]
    // y   = yoe + era*400                     (shifted year)
    // doy = doe - (365*yoe + yoe div 4 - yoe div 100)                     in [0, 365]
    // mp  = (5*doy + 2) div 153                                           in [0, 11]
    // d   = doy - (153*mp + 2) div 5 + 1                                  in [1, 31]
    // mo  = if mp < 10 then mp + 3 else mp - 9                            in [1, 12]
    // yr  = if mp >= 10 then y + 1 else y     (January/February belong to the next shifted year)
    expr* z   = m_arith.mk_add(n, mk_num(719468));
    expr* era = mk_div(z, 146097);
    expr* doe = mk_mod(z, 146097);
    expr* yoe_args[4] = {
        doe,
        m_arith.mk_mul(mk_num(-1), mk_div(doe, 1460)),
        mk_div(doe, 36524),
        m_arith.mk_mul(mk_num(-1), mk_div(doe, 146096))
    };
    expr* yoe = mk_div(m_arith.mk_add(4, yoe_args), 365);
    expr* y   = m_arith.mk_add(yoe, m_arith.mk_mul(mk_num(400), era));
    expr* doy_args[4] = {
        doe,
        m_arith.mk_mul(mk_num(-365), yoe),
        m_arith.mk_mul(mk_num(-1), mk_div(yoe, 4)),
        mk_div(yoe, 100)
    };
    expr* doy = m_arith.mk_add(4, doy_args);
    expr* mp  = mk_div(m_arith.mk_add(m_arith.mk_mul(mk_num(5), doy), mk_num(2)), 153);
    expr* jan_or_feb = m_arith.mk_ge(mp, mk_num(10));
    day   = m_arith.mk_add(
        doy,
        m_arith.mk_mul(mk_num(-1),
                       mk_div(m_arith.mk_add(m_arith.mk_mul(mk_num(153), mp), mk_num(2)), 5)),
        mk_num(1));
    month = m.mk_ite(jan_or_feb,
                     m_arith.mk_sub(mp, mk_num(9)),
                     m_arith.mk_add(mp, mk_num(3)));
    year  = m.mk_ite(jan_or_feb, m_arith.mk_add(y, mk_num(1)), y);
}

// (n + 4) mod 7: day 0 = 1970-01-01 was a Thursday = 4 (0 = Sunday).
expr_ref calendar_rewriter::mk_day_of_week(expr* n) {
    return expr_ref(mk_mod(m_arith.mk_add(n, mk_num(4)), 7), m);
}

br_status calendar_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    expr_ref year(m), month(m), day(m);
    switch (f->get_decl_kind()) {
    case OP_DATE_IS_LEAP_YEAR:
        SASSERT(num_args == 1);
        result = mk_is_leap_year(args[0]);
        return BR_REWRITE_FULL;
    case OP_DATE_DAYS_IN_MONTH:
        SASSERT(num_args == 2);
        result = mk_days_in_month(args[0], args[1]);
        return BR_REWRITE_FULL;
    case OP_DATE_VALID:
        SASSERT(num_args == 3);
        result = mk_valid(args[0], args[1], args[2]);
        return BR_REWRITE_FULL;
    case OP_DATE_TO_EPOCH:
        SASSERT(num_args == 3);
        result = mk_to_epoch(args[0], args[1], args[2]);
        return BR_REWRITE_FULL;
    case OP_DATE_YEAR:
        SASSERT(num_args == 1);
        mk_civil_parts(args[0], year, month, day);
        result = year;
        return BR_REWRITE_FULL;
    case OP_DATE_MONTH:
        SASSERT(num_args == 1);
        mk_civil_parts(args[0], year, month, day);
        result = month;
        return BR_REWRITE_FULL;
    case OP_DATE_DAY:
        SASSERT(num_args == 1);
        mk_civil_parts(args[0], year, month, day);
        result = day;
        return BR_REWRITE_FULL;
    case OP_DATE_DAY_OF_WEEK:
        SASSERT(num_args == 1);
        result = mk_day_of_week(args[0]);
        return BR_REWRITE_FULL;
    default:
        return BR_FAILED;
    }
}
