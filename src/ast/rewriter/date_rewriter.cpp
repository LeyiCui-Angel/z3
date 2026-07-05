/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.cpp

Abstract:

    Basic rewriting rules for the theory of calendar dates.

Author:

    Angel Cui 2026-03-23

--*/
#include "ast/rewriter/date_rewriter.h"

br_status date_rewriter::mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
    SASSERT(f->get_family_id() == get_fid());
    switch (f->get_decl_kind()) {
    case OP_DATE_MK:
        // date.mk is never rewritten; invalid triples are intentionally unspecified.
        return BR_FAILED;
    case OP_DATE_YEAR:
    case OP_DATE_MONTH:
    case OP_DATE_DAY:
        SASSERT(num_args == 1);
        return mk_selector(static_cast<date_op_kind>(f->get_decl_kind()), args[0], result);
    case OP_DATE_ADD:
        SASSERT(num_args == 4);
        return mk_add(args[0], args[1], args[2], args[3], false, result);
    case OP_DATE_SUB:
        SASSERT(num_args == 4);
        return mk_add(args[0], args[1], args[2], args[3], true, result);
    case OP_DATE_LT:
    case OP_DATE_LE:
    case OP_DATE_GT:
    case OP_DATE_GE:
        SASSERT(num_args == 2);
        return mk_cmp(static_cast<date_op_kind>(f->get_decl_kind()), args[0], args[1], result);
    default:
        return BR_FAILED;
    }
}

br_status date_rewriter::mk_selector(date_op_kind k, expr* d, expr_ref& result) {
    rational y, mo, dd;
    if (!m_util.is_value_mk(d, y, mo, dd))
        return BR_FAILED;
    switch (k) {
    case OP_DATE_YEAR:  result = m_util.arith().mk_numeral(y, true); break;
    case OP_DATE_MONTH: result = m_util.arith().mk_numeral(mo, true); break;
    default:            result = m_util.arith().mk_numeral(dd, true); break;
    }
    return BR_DONE;
}

br_status date_rewriter::mk_add(expr* d, expr* py, expr* pm, expr* pd, bool sign, expr_ref& result) {
    arith_util& a = m_util.arith();
    rational y, mo, dd, ry, rm, rd;
    bool concrete = m_util.is_value_mk(d, y, mo, dd) &&
        a.is_numeral(py, ry) && a.is_numeral(pm, rm) && a.is_numeral(pd, rd);
    if (concrete) {
        if (sign) {
            ry.neg();
            rm.neg();
            rd.neg();
        }
        rational oy, om, od;
        date_util::add_period(y, mo, dd, ry, rm, rd, oy, om, od);
        result = m_util.mk_mk(a.mk_numeral(oy, true), a.mk_numeral(om, true), a.mk_numeral(od, true));
        return BR_DONE;
    }
    if (sign) {
        // date.sub(d, py, pm, pd) = date.add(d, -py, -pm, -pd)
        auto neg = [&](expr* e) -> expr* {
            rational r;
            if (a.is_numeral(e, r))
                return a.mk_numeral(-r, true);
            return a.mk_uminus(e);
        };
        result = m_util.mk_add(d, neg(py), neg(pm), neg(pd));
        return BR_REWRITE2;
    }
    return BR_FAILED;
}

br_status date_rewriter::mk_cmp(date_op_kind k, expr* a, expr* b, expr_ref& result) {
    if (a == b) {
        result = m().mk_bool_val(k == OP_DATE_LE || k == OP_DATE_GE);
        return BR_DONE;
    }
    rational y1, m1, d1, y2, m2, d2;
    if (!m_util.is_value_mk(a, y1, m1, d1) || !m_util.is_value_mk(b, y2, m2, d2))
        return BR_FAILED;
    if (k == OP_DATE_GT || k == OP_DATE_GE) {
        std::swap(y1, y2);
        std::swap(m1, m2);
        std::swap(d1, d2);
        k = (k == OP_DATE_GT) ? OP_DATE_LT : OP_DATE_LE;
    }
    bool lt = y1 < y2 || (y1 == y2 && (m1 < m2 || (m1 == m2 && d1 < d2)));
    bool eq = y1 == y2 && m1 == m2 && d1 == d2;
    result = m().mk_bool_val(k == OP_DATE_LT ? lt : (lt || eq));
    return BR_DONE;
}
