/*++
Copyright (c) 2026 Theoria

Module Name:

    date_rewriter.cpp

Abstract:

    Rewriting/decision rules for the theory of calendar dates.

Author:

    Claude (Theoria date theory) 2026-07-07

--*/
#include "ast/rewriter/date_rewriter.h"

expr * date_rewriter::mk_idiv(expr * x, int c) {
    return m_arith.mk_idiv(x, m_arith.mk_int(c));
}

expr * date_rewriter::mk_mod(expr * x, int c) {
    return m_arith.mk_mod(x, m_arith.mk_int(c));
}

expr * date_rewriter::mk_mul(int c, expr * x) {
    return m_arith.mk_mul(m_arith.mk_int(c), x);
}

// Days since 1970-01-01 of the civil date y-m-d (proleptic Gregorian).
// Follows Howard Hinnant's days_from_civil, using floor-based div/mod
// (SMT-LIB div/mod by a positive constant is floor-based).
//
//   yy  = if m <= 2 then y - 1 else y        -- shift to March-based year
//   era = yy div 400,  yoe = yy mod 400      -- yoe in [0, 399]
//   mp  = if m <= 2 then m + 9 else m - 3    -- March-based month, in [0,11]
//                                               for m in [1,12]
//   doy = (153*mp + 2) div 5 + d - 1
//   doe = 365*yoe + yoe div 4 - yoe div 100 + doy
//   days = 146097*era + doe - 719468
expr * date_rewriter::mk_days_from_civil(expr * y, expr * mo, expr * d) {
    expr * two = m_arith.mk_int(2);
    expr_ref janfeb(m_arith.mk_le(mo, two), m);
    expr_ref yy(m.mk_ite(janfeb, m_arith.mk_sub(y, m_arith.mk_int(1)), y), m);
    expr_ref era(mk_idiv(yy, 400), m);
    expr_ref yoe(mk_mod(yy, 400), m);
    expr_ref mp(m.mk_ite(janfeb, m_arith.mk_add(mo, m_arith.mk_int(9)), m_arith.mk_sub(mo, m_arith.mk_int(3))), m);
    expr_ref doy(m_arith.mk_add(mk_idiv(m_arith.mk_add(mk_mul(153, mp), m_arith.mk_int(2)), 5),
                                d,
                                m_arith.mk_int(-1)), m);
    expr * doe_args[4] = { mk_mul(365, yoe), mk_idiv(yoe, 4),
                           m_arith.mk_mul(m_arith.mk_int(-1), mk_idiv(yoe, 100)), doy };
    expr_ref doe(m_arith.mk_add(4, doe_args), m);
    return m_arith.mk_add(mk_mul(146097, era), doe, m_arith.mk_int(-719468));
}

// Shared pieces of Hinnant's civil_from_days for z = days since 1970-01-01:
//   zp  = z + 719468
//   era = zp div 146097, doe = zp mod 146097          -- doe in [0, 146096]
//   yoe = (doe - doe div 1460 + doe div 36524 - doe div 146096) div 365
//   doy = doe - (365*yoe + yoe div 4 - yoe div 100)   -- in [0, 365]
//   mp  = (5*doy + 2) div 153                         -- in [0, 11]
// and the March-based year is yoe + 400*era.
void date_rewriter::mk_civil_parts(expr * z, expr_ref & mp, expr_ref & doy, expr_ref & march_year) {
    expr_ref zp(m_arith.mk_add(z, m_arith.mk_int(719468)), m);
    expr_ref era(mk_idiv(zp, 146097), m);
    expr_ref doe(mk_mod(zp, 146097), m);
    expr * yoe_args[4] = { doe,
                           m_arith.mk_mul(m_arith.mk_int(-1), mk_idiv(doe, 1460)),
                           mk_idiv(doe, 36524),
                           m_arith.mk_mul(m_arith.mk_int(-1), mk_idiv(doe, 146096)) };
    expr_ref yoe_num(m_arith.mk_add(4, yoe_args), m);
    expr_ref yoe(mk_idiv(yoe_num, 365), m);
    doy = m_arith.mk_sub(doe, m_arith.mk_add(mk_mul(365, yoe), mk_idiv(yoe, 4),
                                             m_arith.mk_mul(m_arith.mk_int(-1), mk_idiv(yoe, 100))));
    mp = mk_idiv(m_arith.mk_add(mk_mul(5, doy), m_arith.mk_int(2)), 153);
    march_year = m_arith.mk_add(yoe, mk_mul(400, era));
}

// (or (= 0 (mod y 400)) (and (= 0 (mod y 4)) (not (= 0 (mod y 100)))))
expr * date_rewriter::mk_leap_year(expr * y) {
    expr * zero = m_arith.mk_int(0);
    return m.mk_or(m.mk_eq(mk_mod(y, 400), zero),
                   m.mk_and(m.mk_eq(mk_mod(y, 4), zero),
                            m.mk_not(m.mk_eq(mk_mod(y, 100), zero))));
}

br_status date_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    switch (f->get_decl_kind()) {
    case OP_DATE_MK:
        SASSERT(num_args == 3);
        result = m_util.mk_from_days(mk_days_from_civil(args[0], args[1], args[2]));
        return BR_REWRITE_FULL;
    case OP_DATE_TO_DAYS: {
        SASSERT(num_args == 1);
        expr * x = nullptr;
        if (m_util.is_from_days(args[0], x)) {
            result = x;
            return BR_DONE;
        }
        expr * c = nullptr, * t = nullptr, * e = nullptr;
        if (m.is_ite(args[0], c, t, e)) {
            result = m.mk_ite(c, m_util.mk_to_days(t), m_util.mk_to_days(e));
            return BR_REWRITE_FULL;
        }
        // to_days of an uninterpreted Date term: kept as the integer proxy
        // of its argument.
        return BR_FAILED;
    }
    case OP_DATE_FROM_DAYS:
        // constructor / value form
        return BR_FAILED;
    case OP_DATE_ADD_DAYS:
        SASSERT(num_args == 2);
        result = m_util.mk_from_days(m_arith.mk_add(m_util.mk_to_days(args[0]), args[1]));
        return BR_REWRITE_FULL;
    case OP_DATE_SUB:
        SASSERT(num_args == 2);
        result = m_arith.mk_sub(m_util.mk_to_days(args[0]), m_util.mk_to_days(args[1]));
        return BR_REWRITE_FULL;
    case OP_DATE_LT:
        SASSERT(num_args == 2);
        result = m_arith.mk_lt(m_util.mk_to_days(args[0]), m_util.mk_to_days(args[1]));
        return BR_REWRITE_FULL;
    case OP_DATE_LE:
        SASSERT(num_args == 2);
        result = m_arith.mk_le(m_util.mk_to_days(args[0]), m_util.mk_to_days(args[1]));
        return BR_REWRITE_FULL;
    case OP_DATE_DOW:
        // 1970-01-01 is a Thursday; ISO-8601: 1 = Monday, ..., 7 = Sunday.
        SASSERT(num_args == 1);
        result = m_arith.mk_add(mk_mod(m_arith.mk_add(m_util.mk_to_days(args[0]), m_arith.mk_int(3)), 7),
                                m_arith.mk_int(1));
        return BR_REWRITE_FULL;
    case OP_DATE_YEAR: {
        SASSERT(num_args == 1);
        expr_ref mp(m), doy(m), march_year(m);
        mk_civil_parts(m_util.mk_to_days(args[0]), mp, doy, march_year);
        // month = mp + 3 if mp < 10 else mp - 9; year adds 1 for Jan/Feb,
        // i.e. exactly when mp >= 10.
        result = m.mk_ite(m_arith.mk_ge(mp, m_arith.mk_int(10)),
                          m_arith.mk_add(march_year, m_arith.mk_int(1)),
                          march_year);
        return BR_REWRITE_FULL;
    }
    case OP_DATE_MONTH: {
        SASSERT(num_args == 1);
        expr_ref mp(m), doy(m), march_year(m);
        mk_civil_parts(m_util.mk_to_days(args[0]), mp, doy, march_year);
        result = m.mk_ite(m_arith.mk_lt(mp, m_arith.mk_int(10)),
                          m_arith.mk_add(mp, m_arith.mk_int(3)),
                          m_arith.mk_sub(mp, m_arith.mk_int(9)));
        return BR_REWRITE_FULL;
    }
    case OP_DATE_DAY: {
        SASSERT(num_args == 1);
        expr_ref mp(m), doy(m), march_year(m);
        mk_civil_parts(m_util.mk_to_days(args[0]), mp, doy, march_year);
        result = m_arith.mk_add(doy,
                                m_arith.mk_mul(m_arith.mk_int(-1),
                                               mk_idiv(m_arith.mk_add(mk_mul(153, mp), m_arith.mk_int(2)), 5)),
                                m_arith.mk_int(1));
        return BR_REWRITE_FULL;
    }
    case OP_DATE_VALID: {
        SASSERT(num_args == 3);
        expr * y = args[0], * mo = args[1], * d = args[2];
        expr * one = m_arith.mk_int(1);
        expr * is31_args[7] = { m.mk_eq(mo, m_arith.mk_int(1)),
                                m.mk_eq(mo, m_arith.mk_int(3)),
                                m.mk_eq(mo, m_arith.mk_int(5)),
                                m.mk_eq(mo, m_arith.mk_int(7)),
                                m.mk_eq(mo, m_arith.mk_int(8)),
                                m.mk_eq(mo, m_arith.mk_int(10)),
                                m.mk_eq(mo, m_arith.mk_int(12)) };
        expr_ref is31(m.mk_or(7, is31_args), m);
        expr_ref feb_len(m.mk_ite(mk_leap_year(y), m_arith.mk_int(29), m_arith.mk_int(28)), m);
        expr_ref month_len(m.mk_ite(is31, m_arith.mk_int(31),
                                    m.mk_ite(m.mk_eq(mo, m_arith.mk_int(2)), feb_len, m_arith.mk_int(30))), m);
        expr * valid_args[4] = { m_arith.mk_le(one, mo), m_arith.mk_le(mo, m_arith.mk_int(12)),
                                 m_arith.mk_le(one, d), m_arith.mk_le(d, month_len) };
        result = m.mk_and(std::span<expr* const>(valid_args, 4));
        return BR_REWRITE_FULL;
    }
    case OP_DATE_LEAP_YEAR:
        SASSERT(num_args == 1);
        result = mk_leap_year(args[0]);
        return BR_REWRITE_FULL;
    default:
        return BR_FAILED;
    }
}

br_status date_rewriter::mk_eq_core(expr * a, expr * b, expr_ref & result) {
    SASSERT(m_util.is_date(a) && m_util.is_date(b));
    if (a == b) {
        result = m.mk_true();
        return BR_DONE;
    }
    // to_days is a bijection between Date and Int.
    result = m.mk_eq(m_util.mk_to_days(a), m_util.mk_to_days(b));
    return BR_REWRITE_FULL;
}

br_status date_rewriter::mk_distinct_core(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args > 0 && m_util.is_date(args[0]));
    expr_ref_vector days(m);
    for (unsigned i = 0; i < num_args; ++i)
        days.push_back(m_util.mk_to_days(args[i]));
    result = m.mk_distinct(num_args, days.data());
    return BR_REWRITE_FULL;
}
