/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.cpp

Abstract:

    Rewriting (constant folding) rules for the theory of calendar dates.

Author:

    Angel Cui's date theory task 2026-07-04

--*/
#include "ast/rewriter/date_rewriter.h"

br_status date_rewriter::mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
    SASSERT(f->get_family_id() == get_fid());
    switch (f->get_decl_kind()) {
    case OP_DATE_MK:
        SASSERT(num_args == 3);
        return mk_date_mk(args[0], args[1], args[2], result);
    case OP_DATE_YEAR:
    case OP_DATE_MONTH:
    case OP_DATE_DAY:
        SASSERT(num_args == 1);
        return mk_date_selector(f->get_decl_kind(), args[0], result);
    case OP_DATE_ADD:
        SASSERT(num_args == 4);
        return mk_date_add(false, args[0], args[1], args[2], args[3], result);
    case OP_DATE_SUB:
        SASSERT(num_args == 4);
        return mk_date_add(true, args[0], args[1], args[2], args[3], result);
    case OP_DATE_LT:
    case OP_DATE_LE:
    case OP_DATE_GT:
    case OP_DATE_GE:
        SASSERT(num_args == 2);
        return mk_date_cmp(f->get_decl_kind(), args[0], args[1], result);
    case OP_DATE_EPOCH:
        SASSERT(num_args == 1);
        return mk_date_epoch(args[0], result);
    default:
        return BR_FAILED;
    }
}

br_status date_rewriter::mk_date_mk(expr* y, expr* mo, expr* d, expr_ref& result) {
    arith_util& a = u.arith();
    rational ry, rm, rd;
    if (!a.is_numeral(y, ry) || !ry.is_int() ||
        !a.is_numeral(mo, rm) || !rm.is_int() ||
        !a.is_numeral(d, rd) || !rd.is_int())
        return BR_FAILED;
    rational n = date_decl_plugin::civil_to_days(ry, rm, rd);
    rational ny, nm, nd;
    date_decl_plugin::days_to_civil(n, ny, nm, nd);
    if (ny == ry && nm == rm && nd == rd)
        return BR_FAILED; // already a normalized value
    result = u.mk_value_from_epoch(n);
    return BR_DONE;
}

br_status date_rewriter::mk_date_selector(decl_kind k, expr* d, expr_ref& result) {
    arith_util& a = u.arith();
    rational ry, rm, rd;
    if (!u.is_numeral_mk(d, ry, rm, rd))
        return BR_FAILED;
    rational n = date_decl_plugin::civil_to_days(ry, rm, rd);
    rational ny, nm, nd;
    date_decl_plugin::days_to_civil(n, ny, nm, nd);
    switch (k) {
    case OP_DATE_YEAR:  result = a.mk_numeral(ny, true); break;
    case OP_DATE_MONTH: result = a.mk_numeral(nm, true); break;
    case OP_DATE_DAY:   result = a.mk_numeral(nd, true); break;
    default: UNREACHABLE();
    }
    return BR_DONE;
}

br_status date_rewriter::mk_date_add(bool sub, expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    arith_util& a = u.arith();
    rational rpy, rpm, rpd;
    bool ground_off =
        a.is_numeral(py, rpy) && rpy.is_int() &&
        a.is_numeral(pm, rpm) && rpm.is_int() &&
        a.is_numeral(pd, rpd) && rpd.is_int();
    if (ground_off && rpy.is_zero() && rpm.is_zero() && rpd.is_zero()) {
        // adding or subtracting nothing is the identity, even on symbolic dates
        result = d;
        return BR_DONE;
    }
    rational ry, rm, rd;
    if (!ground_off || !u.is_numeral_mk(d, ry, rm, rd))
        return BR_FAILED;
    if (sub) {
        rpy.neg();
        rpm.neg();
        rpd.neg();
    }
    rational n = date_decl_plugin::civil_to_days(ry, rm, rd);
    result = u.mk_value_from_epoch(date_decl_plugin::add_to_days(n, rpy, rpm, rpd));
    return BR_DONE;
}

br_status date_rewriter::mk_date_cmp(decl_kind k, expr* a, expr* b, expr_ref& result) {
    // normalize gt/ge to lt/le
    if (k == OP_DATE_GT) {
        result = u.mk_lt(b, a);
        return BR_REWRITE1;
    }
    if (k == OP_DATE_GE) {
        result = u.mk_le(b, a);
        return BR_REWRITE1;
    }
    if (a == b) {
        result = m.mk_bool_val(k == OP_DATE_LE);
        return BR_DONE;
    }
    rational y1, m1, d1, y2, m2, d2;
    if (!u.is_numeral_mk(a, y1, m1, d1) || !u.is_numeral_mk(b, y2, m2, d2))
        return BR_FAILED;
    rational n1 = date_decl_plugin::civil_to_days(y1, m1, d1);
    rational n2 = date_decl_plugin::civil_to_days(y2, m2, d2);
    result = m.mk_bool_val(k == OP_DATE_LT ? n1 < n2 : n1 <= n2);
    return BR_DONE;
}

br_status date_rewriter::mk_date_epoch(expr* d, expr_ref& result) {
    rational ry, rm, rd;
    if (!u.is_numeral_mk(d, ry, rm, rd))
        return BR_FAILED;
    result = u.arith().mk_numeral(date_decl_plugin::civil_to_days(ry, rm, rd), true);
    return BR_DONE;
}
