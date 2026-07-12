/*++
Copyright (c) 2026 Theoria contributors

Module Name:

    calendar_rewriter.cpp

Abstract:

    Rewriting rules for the theory of calendar dates.

    The conversions between (year, month, day) triples and epoch day
    numbers follow Howard Hinnant's civil-from-days / days-from-civil
    algorithms for the proleptic Gregorian calendar, restated over
    SMT-LIB integer div/mod.  For a positive numeric divisor n,
    SMT-LIB (div x n) is floor(x/n) and (mod x n) is in [0, n-1] for
    every integer x, so the era/year-of-era decomposition needs no
    case split on the sign of the year and the definitions are total
    on all integer inputs.

Author:

    Claude (Theoria) 2026-07-12

--*/

#include "ast/rewriter/calendar_rewriter.h"
#include "ast/ast_util.h"

expr * calendar_rewriter::mk_div(expr * x, int c) {
    return m_arith.mk_idiv(x, mk_int(c));
}

expr * calendar_rewriter::mk_mod(expr * x, int c) {
    return m_arith.mk_mod(x, mk_int(c));
}

// epoch day number (days since 1970-01-01) of the date y-mo-d
expr * calendar_rewriter::mk_epoch(expr * y, expr * mo, expr * d) {
    expr_ref mo_le_2(m_arith.mk_le(mo, mk_int(2)), m);
    expr_ref yadj(m.mk_ite(mo_le_2, m_arith.mk_sub(y, mk_int(1)), y), m);
    expr_ref era(mk_div(yadj, 400), m);
    expr_ref yoe(mk_mod(yadj, 400), m);
    // month index with March = 0: mp = m > 2 ? m - 3 : m + 9
    expr_ref mp(m.mk_ite(mo_le_2, m_arith.mk_add(mo, mk_int(9)), m_arith.mk_sub(mo, mk_int(3))), m);
    // day of year (March 1 = 0): (153*mp + 2)/5 + d - 1
    expr_ref doy(m_arith.mk_add(mk_div(m_arith.mk_add(m_arith.mk_mul(mk_int(153), mp), mk_int(2)), 5),
                                m_arith.mk_sub(d, mk_int(1))), m);
    // day of era: 365*yoe + yoe/4 - yoe/100 + doy
    expr_ref doe(m_arith.mk_add(m_arith.mk_mul(mk_int(365), yoe),
                                m_arith.mk_sub(mk_div(yoe, 4), mk_div(yoe, 100)),
                                doy), m);
    return m_arith.mk_add(m_arith.mk_mul(mk_int(146097), era), doe, mk_int(-719468));
}

// inverse conversion: the unique valid (y, mo, d) with epoch day number e
void calendar_rewriter::mk_civil(expr * e, expr_ref & y, expr_ref & mo, expr_ref & d) {
    expr_ref z(m_arith.mk_add(e, mk_int(719468)), m);
    expr_ref era(mk_div(z, 146097), m);
    expr_ref doe(mk_mod(z, 146097), m);
    // year of era: (doe - doe/1460 + doe/36524 - doe/146096) / 365
    expr_ref yoe(mk_div(m_arith.mk_add(m_arith.mk_sub(doe, mk_div(doe, 1460)),
                                       m_arith.mk_sub(mk_div(doe, 36524), mk_div(doe, 146096))), 365), m);
    // day of year (March 1 = 0): doe - (365*yoe + yoe/4 - yoe/100)
    expr_ref doy(m_arith.mk_sub(doe, m_arith.mk_add(m_arith.mk_mul(mk_int(365), yoe),
                                                    m_arith.mk_sub(mk_div(yoe, 4), mk_div(yoe, 100)))), m);
    // month index with March = 0: (5*doy + 2)/153
    expr_ref mp(mk_div(m_arith.mk_add(m_arith.mk_mul(mk_int(5), doy), mk_int(2)), 153), m);
    d = m_arith.mk_add(m_arith.mk_sub(doy, mk_div(m_arith.mk_add(m_arith.mk_mul(mk_int(153), mp), mk_int(2)), 5)),
                       mk_int(1));
    mo = m.mk_ite(m_arith.mk_lt(mp, mk_int(10)),
                  m_arith.mk_add(mp, mk_int(3)),
                  m_arith.mk_sub(mp, mk_int(9)));
    y = m_arith.mk_add(m_arith.mk_mul(mk_int(400), era), yoe,
                       m.mk_ite(m_arith.mk_le(mo, mk_int(2)), mk_int(1), mk_int(0)));
}

expr * calendar_rewriter::mk_leap(expr * y) {
    return m.mk_or(m.mk_eq(mk_mod(y, 400), mk_int(0)),
                   m.mk_and(m.mk_eq(mk_mod(y, 4), mk_int(0)),
                            m.mk_not(m.mk_eq(mk_mod(y, 100), mk_int(0)))));
}

expr * calendar_rewriter::mk_days_in_month(expr * y, expr * mo) {
    expr_ref is_feb(m.mk_eq(mo, mk_int(2)), m);
    expr_ref short_month(m.mk_or(m.mk_eq(mo, mk_int(4)), m.mk_eq(mo, mk_int(6)),
                                 m.mk_eq(mo, mk_int(9)), m.mk_eq(mo, mk_int(11))), m);
    expr_ref feb_days(m.mk_ite(mk_leap(y), mk_int(29), mk_int(28)), m);
    return m.mk_ite(is_feb, feb_days, m.mk_ite(short_month, mk_int(30), mk_int(31)));
}

br_status calendar_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    expr_ref y(m), mo(m), d(m);
    switch (f->get_decl_kind()) {
    case OP_DATE_TO_EPOCH:
        SASSERT(num_args == 3);
        result = mk_epoch(args[0], args[1], args[2]);
        return BR_REWRITE_FULL;
    case OP_DATE_YEAR:
        SASSERT(num_args == 1);
        mk_civil(args[0], y, mo, d);
        result = y;
        return BR_REWRITE_FULL;
    case OP_DATE_MONTH:
        SASSERT(num_args == 1);
        mk_civil(args[0], y, mo, d);
        result = mo;
        return BR_REWRITE_FULL;
    case OP_DATE_DAY:
        SASSERT(num_args == 1);
        mk_civil(args[0], y, mo, d);
        result = d;
        return BR_REWRITE_FULL;
    case OP_DATE_DAY_OF_WEEK:
        // 1970-01-01 (epoch day 0) was a Thursday; 0 = Sunday
        SASSERT(num_args == 1);
        result = mk_mod(m_arith.mk_add(args[0], mk_int(4)), 7);
        return BR_REWRITE_FULL;
    case OP_DATE_LEAP_YEAR:
        SASSERT(num_args == 1);
        result = mk_leap(args[0]);
        return BR_REWRITE_FULL;
    case OP_DATE_DAYS_IN_MONTH:
        SASSERT(num_args == 2);
        result = mk_days_in_month(args[0], args[1]);
        return BR_REWRITE_FULL;
    case OP_DATE_VALID:
        SASSERT(num_args == 3);
        result = m.mk_and(m_arith.mk_le(mk_int(1), args[1]),
                          m_arith.mk_le(args[1], mk_int(12)),
                          m.mk_and(m_arith.mk_le(mk_int(1), args[2]),
                                   m_arith.mk_le(args[2], mk_days_in_month(args[0], args[1]))));
        return BR_REWRITE_FULL;
    default:
        return BR_FAILED;
    }
}
