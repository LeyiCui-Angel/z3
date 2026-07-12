/*++
Copyright (c) 2026 Theoria contributors

Test the theory of calendar dates: the calendar rewriter must agree
with a naive day-counting reference implementation of the proleptic
Gregorian calendar on ground terms.

--*/
#include "ast/calendar_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/ast_pp.h"

namespace {

bool ref_leap(int64_t y) {
    return y % 400 == 0 || (y % 4 == 0 && y % 100 != 0);
}

int ref_days_in_month(int64_t y, int m) {
    if (m == 2)
        return ref_leap(y) ? 29 : 28;
    return (m == 4 || m == 6 || m == 9 || m == 11) ? 30 : 31;
}

// days since 1970-01-01, counted one month at a time
int64_t ref_epoch(int64_t y, int m, int d) {
    int64_t days = 0;
    int64_t yy = 1970;
    int mm = 1;
    while (yy < y || (yy == y && mm < m)) {
        days += ref_days_in_month(yy, mm);
        if (++mm == 13) { mm = 1; ++yy; }
    }
    while (yy > y || (yy == y && mm > m)) {
        if (--mm == 0) { mm = 12; --yy; }
        days -= ref_days_in_month(yy, mm);
    }
    return days + d - 1;
}

rational eval_int(th_rewriter& rw, arith_util& a, expr* e) {
    expr_ref r(rw.m());
    rw(e, r);
    rational v;
    VERIFY(a.is_numeral(r, v));
    return v;
}

bool eval_bool(th_rewriter& rw, expr* e) {
    expr_ref r(rw.m());
    rw(e, r);
    VERIFY(rw.m().is_true(r) || rw.m().is_false(r));
    return rw.m().is_true(r);
}

}

void tst_calendar() {
    ast_manager m;
    reg_decl_plugins(m);
    calendar_util cal(m);
    arith_util a(m);
    th_rewriter rw(m);

    // deterministic pseudo-random walk over a wide range of dates
    uint64_t state = 88172645463325252ull;
    auto rnd = [&]() { state ^= state << 13; state ^= state >> 7; state ^= state << 17; return state; };

    for (unsigned i = 0; i < 4000; ++i) {
        int64_t y = static_cast<int64_t>(rnd() % 4001) - 1000;    // years -1000..3000
        int mo = 1 + static_cast<int>(rnd() % 12);
        int d = 1 + static_cast<int>(rnd() % ref_days_in_month(y, mo));
        int64_t e = ref_epoch(y, mo, d);

        expr_ref ye(a.mk_int(rational(y, rational::i64())), m);
        expr_ref me(a.mk_int(mo), m);
        expr_ref de(a.mk_int(d), m);
        expr_ref ee(a.mk_int(rational(e, rational::i64())), m);

        ENSURE(eval_int(rw, a, cal.mk_to_epoch(ye, me, de)) == rational(e, rational::i64()));
        ENSURE(eval_int(rw, a, cal.mk_year(ee)) == rational(y, rational::i64()));
        ENSURE(eval_int(rw, a, cal.mk_month(ee)) == rational(mo));
        ENSURE(eval_int(rw, a, cal.mk_day(ee)) == rational(d));
        ENSURE(eval_int(rw, a, cal.mk_day_of_week(ee)) == rational(static_cast<int>(((e + 4) % 7 + 7) % 7)));
        ENSURE(eval_bool(rw, cal.mk_leap_year(ye)) == ref_leap(y));
        ENSURE(eval_int(rw, a, cal.mk_days_in_month(ye, me)) == rational(ref_days_in_month(y, mo)));
        ENSURE(eval_bool(rw, cal.mk_valid(ye, me, de)));
        // day 0 and one-past-the-end are invalid
        expr_ref d0(a.mk_int(0), m);
        expr_ref dover(a.mk_int(ref_days_in_month(y, mo) + 1), m);
        ENSURE(!eval_bool(rw, cal.mk_valid(ye, me, d0)));
        ENSURE(!eval_bool(rw, cal.mk_valid(ye, me, dover)));
    }

    // fixed anchors
    ENSURE(eval_int(rw, a, cal.mk_to_epoch(a.mk_int(1970), a.mk_int(1), a.mk_int(1))).is_zero());
    ENSURE(eval_int(rw, a, cal.mk_day_of_week(a.mk_int(0))) == rational(4)); // Thursday
}
