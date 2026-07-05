/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.cpp

Abstract:

    Basic rewriting rules for the theory of calendar dates.

Author:

    Date theory extension 2026-07-05

--*/
#include "ast/rewriter/date_rewriter.h"

br_status date_rewriter::mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
    SASSERT(f->get_family_id() == get_fid());
    switch (f->get_decl_kind()) {
    case OP_DATE_MK:
        return BR_FAILED;
    case OP_DATE_YEAR:
    case OP_DATE_MONTH:
    case OP_DATE_DAY:
        SASSERT(num_args == 1);
        return mk_selector(f->get_decl_kind(), args[0], result);
    case OP_DATE_ADD:
        SASSERT(num_args == 4);
        return mk_add(args[0], args[1], args[2], args[3], result);
    case OP_DATE_SUB:
        SASSERT(num_args == 4);
        return mk_sub(args[0], args[1], args[2], args[3], result);
    case OP_DATE_LT:
    case OP_DATE_LE:
    case OP_DATE_GT:
    case OP_DATE_GE:
        SASSERT(num_args == 2);
        return mk_cmp(f->get_decl_kind(), args[0], args[1], result);
    default:
        return BR_FAILED;
    }
}

br_status date_rewriter::mk_selector(decl_kind k, expr* d, expr_ref& result) {
    // Selectors are only specified on calendar-valid constructor triples.
    rational y, mo, dd;
    if (!m_util.is_date_value(d, y, mo, dd))
        return BR_FAILED;
    switch (k) {
    case OP_DATE_YEAR:  result = m_arith.mk_int(y);  break;
    case OP_DATE_MONTH: result = m_arith.mk_int(mo); break;
    case OP_DATE_DAY:   result = m_arith.mk_int(dd); break;
    default: return BR_FAILED;
    }
    return BR_DONE;
}

br_status date_rewriter::mk_add(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    rational ry, rm, rd, vy, vm, vd;
    bool zero_period =
        m_arith.is_numeral(py, ry) && ry.is_zero() &&
        m_arith.is_numeral(pm, rm) && rm.is_zero() &&
        m_arith.is_numeral(pd, rd) && rd.is_zero();
    if (zero_period) {
        // adding the zero period is the identity on (valid) dates
        result = d;
        return BR_DONE;
    }
    if (m_util.is_date_value(d, vy, vm, vd) &&
        m_arith.is_numeral(py, ry) && ry.is_int() &&
        m_arith.is_numeral(pm, rm) && rm.is_int() &&
        m_arith.is_numeral(pd, rd) && rd.is_int()) {
        date_util::add_period(vy, vm, vd, ry, rm, rd);
        result = m_util.mk_date_value(vy, vm, vd);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status date_rewriter::mk_sub(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    // date.sub(d, py, pm, pd) = date.add(d, -py, -pm, -pd)
    expr_ref npy(m), npm(m), npd(m);
    rational r;
    auto neg = [&](expr* e, expr_ref& out) {
        if (m_arith.is_numeral(e, r))
            out = m_arith.mk_int(-r);
        else
            out = m_arith.mk_uminus(e);
    };
    neg(py, npy);
    neg(pm, npm);
    neg(pd, npd);
    result = m_util.mk_add(d, npy, npm, npd);
    return BR_REWRITE2;
}

expr* date_rewriter::mk_lex_lt(expr* a, expr* b, bool strict) {
    expr* y1 = m_util.mk_year(a),  *y2 = m_util.mk_year(b);
    expr* m1 = m_util.mk_month(a), *m2 = m_util.mk_month(b);
    expr* d1 = m_util.mk_day(a),   *d2 = m_util.mk_day(b);
    expr* last = strict ? m_arith.mk_lt(d1, d2) : m_arith.mk_le(d1, d2);
    return m.mk_or(
        m_arith.mk_lt(y1, y2),
        m.mk_and(m.mk_eq(y1, y2), m_arith.mk_lt(m1, m2)),
        m.mk_and(m.mk_eq(y1, y2), m.mk_eq(m1, m2), last));
}

br_status date_rewriter::mk_cmp(decl_kind k, expr* a, expr* b, expr_ref& result) {
    if (a == b) {
        result = (k == OP_DATE_LE || k == OP_DATE_GE) ? m.mk_true() : m.mk_false();
        return BR_DONE;
    }
    rational y1, m1, d1, y2, m2, d2;
    if (m_util.is_date_value(a, y1, m1, d1) && m_util.is_date_value(b, y2, m2, d2)) {
        bool lt = y1 < y2 || (y1 == y2 && (m1 < m2 || (m1 == m2 && d1 < d2)));
        bool eq = y1 == y2 && m1 == m2 && d1 == d2;
        bool res = false;
        switch (k) {
        case OP_DATE_LT: res = lt; break;
        case OP_DATE_LE: res = lt || eq; break;
        case OP_DATE_GT: res = !lt && !eq; break;
        case OP_DATE_GE: res = !lt; break;
        default: return BR_FAILED;
        }
        result = m.mk_bool_val(res);
        return BR_DONE;
    }
    // expand to the lexicographic order on (year, month, day)
    switch (k) {
    case OP_DATE_LT: result = mk_lex_lt(a, b, true);  break;
    case OP_DATE_LE: result = mk_lex_lt(a, b, false); break;
    case OP_DATE_GT: result = mk_lex_lt(b, a, true);  break;
    case OP_DATE_GE: result = mk_lex_lt(b, a, false); break;
    default: return BR_FAILED;
    }
    return BR_REWRITE_FULL;
}
