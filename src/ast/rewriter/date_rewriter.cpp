/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.cpp

Abstract:

    Basic rewriting rules for the Dates theory.

Author:

    Date theory extension 2026-07-04

--*/
#include "ast/rewriter/date_rewriter.h"

bool date_rewriter::is_valid_value(expr* e, rational& y, rational& mo, rational& d) const {
    return dt.is_numeral_mk(e, y, mo, d) && date_util::is_valid_date(y, mo, d);
}

// days since 1970-01-01 of a valid proleptic Gregorian date
// (Howard Hinnant's days_from_civil, over unbounded integers)
rational date_rewriter::epoch_of(rational const& y, rational const& mo, rational const& d) {
    rational yadj = mo <= rational(2) ? y - rational(1) : y;
    rational era = div(yadj, rational(400));
    rational yoe = yadj - rational(400) * era;                        // [0, 399]
    rational mp = mod(mo + rational(9), rational(12));                // [0, 11]
    rational doy = div(rational(153) * mp + rational(2), rational(5)) + d - rational(1);
    rational doe = rational(365) * yoe + div(yoe, rational(4)) - div(yoe, rational(100)) + doy;
    return rational(146097) * era + doe - rational(719468);
}

// inverse of epoch_of
void date_rewriter::date_of_epoch(rational const& e, rational& y, rational& mo, rational& d) {
    rational z = e + rational(719468);
    rational era = div(z, rational(146097));
    rational doe = z - rational(146097) * era;                        // [0, 146096]
    rational yoe = div(doe - div(doe, rational(1460)) + div(doe, rational(36524)) - div(doe, rational(146096)),
                       rational(365));                                // [0, 399]
    rational y0 = yoe + rational(400) * era;
    rational doy = doe - (rational(365) * yoe + div(yoe, rational(4)) - div(yoe, rational(100)));
    rational mp = div(rational(5) * doy + rational(2), rational(153));
    d = doy - div(rational(153) * mp + rational(2), rational(5)) + rational(1);
    mo = mp < rational(10) ? mp + rational(3) : mp - rational(9);
    y = mo <= rational(2) ? y0 + rational(1) : y0;
}

br_status date_rewriter::mk_add(rational const& y, rational const& mo, rational const& d,
                                rational const& py, rational const& pm, rational const& pd,
                                expr_ref& result) {
    // step 1 -- month normalization
    rational t = mo + rational(12) * py + pm - rational(1);
    rational oy = y + div(t, rational(12));
    rational om = mod(t, rational(12)) + rational(1);
    // step 2 -- end-of-month clamp
    rational dim = date_util::days_in_month(oy, om);
    rational clamp = d < dim ? d : dim;
    // step 3 -- day carry, via the epoch-day bijection
    rational ry, rm, rd;
    date_of_epoch(epoch_of(oy, om, clamp) + pd, ry, rm, rd);
    result = dt.mk_mk(ry, rm, rd);
    return BR_DONE;
}

br_status date_rewriter::mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
    rational y1, m1, d1, y2, m2, d2, py, pm, pd;
    switch (f->get_decl_kind()) {
    case OP_DATE_YEAR:
        if (is_valid_value(args[0], y1, m1, d1)) {
            result = a.mk_int(y1);
            return BR_DONE;
        }
        return BR_FAILED;
    case OP_DATE_MONTH:
        if (is_valid_value(args[0], y1, m1, d1)) {
            result = a.mk_int(m1);
            return BR_DONE;
        }
        return BR_FAILED;
    case OP_DATE_DAY:
        if (is_valid_value(args[0], y1, m1, d1)) {
            result = a.mk_int(d1);
            return BR_DONE;
        }
        return BR_FAILED;
    case OP_DATE_ADD:
        if (is_valid_value(args[0], y1, m1, d1) &&
            a.is_numeral(args[1], py) && a.is_numeral(args[2], pm) && a.is_numeral(args[3], pd))
            return mk_add(y1, m1, d1, py, pm, pd, result);
        return BR_FAILED;
    case OP_DATE_SUB:
        if (is_valid_value(args[0], y1, m1, d1) &&
            a.is_numeral(args[1], py) && a.is_numeral(args[2], pm) && a.is_numeral(args[3], pd))
            return mk_add(y1, m1, d1, -py, -pm, -pd, result);
        return BR_FAILED;
    case OP_DATE_LT:
        if (is_valid_value(args[0], y1, m1, d1) && is_valid_value(args[1], y2, m2, d2)) {
            result = m.mk_bool_val(
                std::tie(y1, m1, d1) < std::tie(y2, m2, d2));
            return BR_DONE;
        }
        return BR_FAILED;
    case OP_DATE_LE:
        if (is_valid_value(args[0], y1, m1, d1) && is_valid_value(args[1], y2, m2, d2)) {
            result = m.mk_bool_val(
                std::tie(y1, m1, d1) <= std::tie(y2, m2, d2));
            return BR_DONE;
        }
        return BR_FAILED;
    case OP_DATE_GT:
        if (is_valid_value(args[0], y1, m1, d1) && is_valid_value(args[1], y2, m2, d2)) {
            result = m.mk_bool_val(
                std::tie(y2, m2, d2) < std::tie(y1, m1, d1));
            return BR_DONE;
        }
        return BR_FAILED;
    case OP_DATE_GE:
        if (is_valid_value(args[0], y1, m1, d1) && is_valid_value(args[1], y2, m2, d2)) {
            result = m.mk_bool_val(
                std::tie(y2, m2, d2) <= std::tie(y1, m1, d1));
            return BR_DONE;
        }
        return BR_FAILED;
    default:
        return BR_FAILED;
    }
}
