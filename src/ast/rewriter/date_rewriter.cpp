/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.cpp

Abstract:

    Basic rewriting rules for the theory of calendar dates.

    Rewrites are only applied to calendar-valid concrete dates; terms
    involving invalid concrete date.mk applications are left untouched so
    that the theory solvers give them their unspecified-but-consistent
    interpretation.

Author:

    Claude (Anthropic) 2026-07-04

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
    case OP_DATE_SUB:
        SASSERT(num_args == 4);
        return mk_add_sub(f->get_decl_kind() == OP_DATE_SUB, args[0], args[1], args[2], args[3], result);
    case OP_DATE_LT:
    case OP_DATE_LE:
    case OP_DATE_GT:
    case OP_DATE_GE:
        SASSERT(num_args == 2);
        return mk_cmp(f->get_decl_kind(), args[0], args[1], result);
    case OP_DATE_EPOCH: {
        SASSERT(num_args == 1);
        rational y, mo, dd;
        if (m_util.eval_ground(args[0], y, mo, dd)) {
            arith_util a(m());
            result = a.mk_int(date_util::civil_to_days(y, mo, dd));
            return BR_DONE;
        }
        return BR_FAILED;
    }
    default:
        UNREACHABLE();
        return BR_FAILED;
    }
}

br_status date_rewriter::mk_selector(decl_kind k, expr* d, expr_ref& result) {
    rational y, mo, dd;
    if (!m_util.is_concrete_mk(d, y, mo, dd) || !date_util::is_valid_date(y, mo, dd))
        return BR_FAILED;
    switch (k) {
    case OP_DATE_YEAR:  result = to_app(d)->get_arg(0); return BR_DONE;
    case OP_DATE_MONTH: result = to_app(d)->get_arg(1); return BR_DONE;
    case OP_DATE_DAY:   result = to_app(d)->get_arg(2); return BR_DONE;
    default: UNREACHABLE(); return BR_FAILED;
    }
}

br_status date_rewriter::mk_add_sub(bool sub, expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    rational y, mo, dd, vy, vm, vd;
    if (!m_util.is_concrete_mk(d, y, mo, dd) || !date_util::is_valid_date(y, mo, dd))
        return BR_FAILED;
    arith_util a(m());
    if (!a.is_numeral(py, vy) || !a.is_numeral(pm, vm) || !a.is_numeral(pd, vd) ||
        !vy.is_int() || !vm.is_int() || !vd.is_int())
        return BR_FAILED;
    if (sub) {
        vy.neg(); vm.neg(); vd.neg();
    }
    rational ry, rm, rd;
    date_util::add_period(y, mo, dd, vy, vm, vd, ry, rm, rd);
    result = m_util.mk_date(ry, rm, rd);
    return BR_DONE;
}

br_status date_rewriter::mk_cmp(decl_kind k, expr* x, expr* y, expr_ref& result) {
    rational y1, m1, d1, y2, m2, d2;
    bool g1 = m_util.is_concrete_mk(x, y1, m1, d1) && date_util::is_valid_date(y1, m1, d1);
    bool g2 = m_util.is_concrete_mk(y, y2, m2, d2) && date_util::is_valid_date(y2, m2, d2);
    if (g1 && g2) {
        rational e1 = date_util::civil_to_days(y1, m1, d1);
        rational e2 = date_util::civil_to_days(y2, m2, d2);
        switch (k) {
        case OP_DATE_LT: result = m().mk_bool_val(e1 < e2); return BR_DONE;
        case OP_DATE_LE: result = m().mk_bool_val(e1 <= e2); return BR_DONE;
        case OP_DATE_GT: result = m().mk_bool_val(e1 > e2); return BR_DONE;
        case OP_DATE_GE: result = m().mk_bool_val(e1 >= e2); return BR_DONE;
        default: UNREACHABLE(); return BR_FAILED;
        }
    }
    if (x == y) {
        // the order is reflexive on every date value
        switch (k) {
        case OP_DATE_LT:
        case OP_DATE_GT: result = m().mk_false(); return BR_DONE;
        case OP_DATE_LE:
        case OP_DATE_GE: result = m().mk_true(); return BR_DONE;
        default: UNREACHABLE(); return BR_FAILED;
        }
    }
    return BR_FAILED;
}
