/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.cpp

Abstract:

    Basic rewriting rules for date terms.

Author:

    Claude 2026-07-04

--*/
#include "ast/rewriter/date_rewriter.h"

br_status date_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    switch (f->get_decl_kind()) {
    case OP_DATE_MK:
        SASSERT(num_args == 3);
        return mk_date_mk(args[0], args[1], args[2], result);
    case OP_DATE_YEAR:
    case OP_DATE_MONTH:
    case OP_DATE_DAY:
    case OP_DATE_RATA:
        SASSERT(num_args == 1);
        return mk_date_selector(f->get_decl_kind(), args[0], result);
    case OP_DATE_ADD:
        SASSERT(num_args == 4);
        return mk_date_add(args[0], args[1], args[2], args[3], result);
    case OP_DATE_SUB:
        SASSERT(num_args == 4);
        return mk_date_sub(args[0], args[1], args[2], args[3], result);
    case OP_DATE_LT:
    case OP_DATE_LE:
    case OP_DATE_GT:
    case OP_DATE_GE:
        SASSERT(num_args == 2);
        return mk_date_cmp(f->get_decl_kind(), args[0], args[1], result);
    default:
        return BR_FAILED;
    }
}

br_status date_rewriter::mk_date_mk(expr* y, expr* mo, expr* d, expr_ref& result) {
    arith_util& a = m_util.arith();
    rational ry, rm, rd;
    if (!a.is_numeral(y, ry) || !ry.is_int() ||
        !a.is_numeral(mo, rm) || !rm.is_int() ||
        !a.is_numeral(d, rd) || !rd.is_int())
        return BR_FAILED;
    if (date_util::is_valid_date(ry, rm, rd))
        return BR_FAILED; // already a canonical value
    // direct constructor application on an invalid triple: fold to the fixed
    // total interpretation so every concrete date.mk denotes a valid date
    date_util::normalize_mk(ry, rm, rd);
    result = m_util.mk_date_value(ry, rm, rd);
    return BR_DONE;
}

br_status date_rewriter::mk_date_selector(decl_kind k, expr* a, expr_ref& result) {
    rational y, mo, d;
    // selector values are only specified for calendar-valid constructor triples
    if (!m_util.is_value_mk(a, y, mo, d))
        return BR_FAILED;
    switch (k) {
    case OP_DATE_YEAR:  result = m_util.arith().mk_int(y);  break;
    case OP_DATE_MONTH: result = m_util.arith().mk_int(mo); break;
    case OP_DATE_DAY:   result = m_util.arith().mk_int(d);  break;
    case OP_DATE_RATA:  result = m_util.arith().mk_int(date_util::rata_die(y, mo, d)); break;
    default: return BR_FAILED;
    }
    return BR_DONE;
}

br_status date_rewriter::mk_date_add(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    arith_util& a = m_util.arith();
    rational y, mo, dd, ny, nm, nd;
    rational vy, vm, vd;
    if (!m_util.is_value_mk(d, y, mo, dd))
        return BR_FAILED;
    if (!a.is_numeral(py, vy) || !vy.is_int() ||
        !a.is_numeral(pm, vm) || !vm.is_int() ||
        !a.is_numeral(pd, vd) || !vd.is_int())
        return BR_FAILED;
    date_util::add_period(y, mo, dd, vy, vm, vd, ny, nm, nd);
    result = m_util.mk_date_value(ny, nm, nd);
    return BR_DONE;
}

br_status date_rewriter::mk_date_sub(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    // date.sub(d, py, pm, pd) = date.add(d, -py, -pm, -pd)
    arith_util& a = m_util.arith();
    expr_ref npy(a.mk_uminus(py), m), npm(a.mk_uminus(pm), m), npd(a.mk_uminus(pd), m);
    expr* args[4] = { d, npy, npm, npd };
    result = m.mk_app(get_fid(), OP_DATE_ADD, 4, args);
    return BR_REWRITE_FULL;
}

br_status date_rewriter::mk_date_cmp(decl_kind k, expr* a, expr* b, expr_ref& result) {
    // normalize gt/ge to lt/le with swapped arguments
    if (k == OP_DATE_GT || k == OP_DATE_GE) {
        expr* args[2] = { b, a };
        result = m.mk_app(get_fid(), k == OP_DATE_GT ? OP_DATE_LT : OP_DATE_LE, 2, args);
        return BR_REWRITE1;
    }
    if (a == b) {
        result = k == OP_DATE_LE ? m.mk_true() : m.mk_false();
        return BR_DONE;
    }
    rational y1, m1, d1, y2, m2, d2;
    if (m_util.is_value_mk(a, y1, m1, d1) && m_util.is_value_mk(b, y2, m2, d2)) {
        // lexicographic comparison on (year, month, day)
        bool lt = y1 < y2 || (y1 == y2 && (m1 < m2 || (m1 == m2 && d1 < d2)));
        bool eq = y1 == y2 && m1 == m2 && d1 == d2;
        result = m.mk_bool_val(k == OP_DATE_LT ? lt : (lt || eq));
        return BR_DONE;
    }
    return BR_FAILED;
}
