/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.cpp

Abstract:

    Basic rewriting rules for dates.

Author:

    Date theory extension 2026-07-05

--*/
#include "ast/rewriter/date_rewriter.h"

br_status date_rewriter::mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
    SASSERT(f->get_family_id() == get_fid());
    switch (f->get_decl_kind()) {
    case OP_DATE_MK:
        SASSERT(num_args == 3);
        return mk_mk(args[0], args[1], args[2], result);
    case OP_DATE_MK0:
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
        return mk_compare(f->get_decl_kind(), args[0], args[1], result);
    default:
        return BR_FAILED;
    }
}

br_status date_rewriter::mk_mk(expr* y, expr* mo, expr* d, expr_ref& result) {
    rational ny, nm, nd;
    arith_util& a = m_util.arith();
    // A direct application of date.mk to a calendar-invalid concrete triple
    // is unspecified: canonicalize it to the uninterpreted fallback
    // date.mk0, whose value is an arbitrary calendar-valid date chosen by
    // the solver and recorded in the model.
    if (a.is_numeral(y, ny) && ny.is_int() &&
        a.is_numeral(mo, nm) && nm.is_int() &&
        a.is_numeral(d, nd) && nd.is_int() &&
        !date_util::is_valid_date(ny, nm, nd)) {
        result = m_util.mk_date0(y, mo, d);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status date_rewriter::mk_selector(decl_kind k, expr* arg, expr_ref& result) {
    rational y, mo, d;
    // selectors are only specified on calendar-valid constructor triples
    if (!m_util.is_concrete_date(arg, y, mo, d) || !date_util::is_valid_date(y, mo, d))
        return BR_FAILED;
    switch (k) {
    case OP_DATE_YEAR:  result = m_util.arith().mk_int(y);  break;
    case OP_DATE_MONTH: result = m_util.arith().mk_int(mo); break;
    case OP_DATE_DAY:   result = m_util.arith().mk_int(d);  break;
    default: UNREACHABLE();
    }
    return BR_DONE;
}

br_status date_rewriter::mk_add(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    rational y, mo, dy, vy, vm, vd;
    arith_util& a = m_util.arith();
    if (m_util.is_concrete_date(d, y, mo, dy) && date_util::is_valid_date(y, mo, dy) &&
        a.is_numeral(py, vy) && vy.is_int() &&
        a.is_numeral(pm, vm) && vm.is_int() &&
        a.is_numeral(pd, vd) && vd.is_int()) {
        rational oy, om, od;
        date_util::add_period(y, mo, dy, vy, vm, vd, oy, om, od);
        result = m_util.mk_date(oy, om, od);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status date_rewriter::mk_sub(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    // date.sub(d, py, pm, pd) = date.add(d, -py, -pm, -pd)
    arith_util& a = m_util.arith();
    result = m_util.mk_add(d, a.mk_uminus(py), a.mk_uminus(pm), a.mk_uminus(pd));
    return BR_REWRITE2;
}

br_status date_rewriter::mk_compare(decl_kind k, expr* x, expr* y, expr_ref& result) {
    ast_manager& m = this->m();
    // normalize gt/ge to lt/le with swapped arguments
    if (k == OP_DATE_GT) {
        result = m_util.mk_lt(y, x);
        return BR_REWRITE1;
    }
    if (k == OP_DATE_GE) {
        result = m_util.mk_le(y, x);
        return BR_REWRITE1;
    }
    if (x == y) {
        result = k == OP_DATE_LT ? m.mk_false() : m.mk_true();
        return BR_DONE;
    }
    rational y1, m1, d1, y2, m2, d2;
    if (m_util.is_concrete_date(x, y1, m1, d1) && date_util::is_valid_date(y1, m1, d1) &&
        m_util.is_concrete_date(y, y2, m2, d2) && date_util::is_valid_date(y2, m2, d2)) {
        rational e1 = date_util::epoch_of_civil(y1, m1, d1);
        rational e2 = date_util::epoch_of_civil(y2, m2, d2);
        result = m.mk_bool_val(k == OP_DATE_LT ? e1 < e2 : e1 <= e2);
        return BR_DONE;
    }
    return BR_FAILED;
}
