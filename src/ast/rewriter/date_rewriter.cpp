/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.cpp

Abstract:

    Rewriting rules for date terms.

Author:

    Z3 date theory extension 2026-07-05

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
        return mk_date_selector(static_cast<date_op_kind>(f->get_decl_kind()), args[0], result);
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
        return mk_date_cmp(static_cast<date_op_kind>(f->get_decl_kind()), args[0], args[1], result);
    case OP_DATE_EPOCH:
        SASSERT(num_args == 1);
        return mk_date_epoch(args[0], result);
    default:
        return BR_FAILED;
    }
}

/**
   \brief Epoch day of a date given as date.mk over numerals forming a
   valid civil date. Invalid components have no date value; terms built
   from them are left to the theory solvers, whose validity axioms make
   the constraints unsatisfiable.
*/
bool date_rewriter::date_epoch_value(expr* e, rational& z) const {
    return m_util.is_date_value(e, z);
}

br_status date_rewriter::mk_date_mk(expr* y, expr* mo, expr* d, expr_ref& result) {
    // constructor-selector roundtrip: (date.mk (date.year x) (date.month x) (date.day x)) = x
    if (m_util.is_year(y) && m_util.is_month(mo) && m_util.is_day(d)) {
        expr* x = to_app(y)->get_arg(0);
        if (x == to_app(mo)->get_arg(0) && x == to_app(d)->get_arg(0)) {
            result = x;
            return BR_DONE;
        }
    }
    // date.mk over numerals is already in normal form: valid triples are
    // canonical date values, invalid ones denote no date (strict semantics)
    return BR_FAILED;
}

br_status date_rewriter::mk_date_selector(date_op_kind k, expr* d, expr_ref& result) {
    rational z;
    if (!date_epoch_value(d, z))
        return BR_FAILED;
    rational y, mo, dd;
    date_util::civil_of_epoch(z, y, mo, dd);
    arith_util& a = m_util.arith();
    switch (k) {
    case OP_DATE_YEAR:  result = a.mk_int(y); break;
    case OP_DATE_MONTH: result = a.mk_int(mo); break;
    case OP_DATE_DAY:   result = a.mk_int(dd); break;
    default: UNREACHABLE();
    }
    return BR_DONE;
}

br_status date_rewriter::mk_date_add(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    rational z, ry, rm, rd;
    arith_util& a = m_util.arith();
    if (!date_epoch_value(d, z))
        return BR_FAILED;
    if (!a.is_numeral(py, ry) || !a.is_numeral(pm, rm) || !a.is_numeral(pd, rd))
        return BR_FAILED;
    result = m_util.mk_date_value(date_util::add_to_epoch(z, ry, rm, rd));
    return BR_DONE;
}

br_status date_rewriter::mk_date_sub(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    // date.sub is date.add with negated offsets by definition
    arith_util& a = m_util.arith();
    expr_ref npy(a.mk_uminus(py), m);
    expr_ref npm(a.mk_uminus(pm), m);
    expr_ref npd(a.mk_uminus(pd), m);
    expr* args[4] = { d, npy, npm, npd };
    result = m.mk_app(get_fid(), OP_DATE_ADD, 4, args);
    return BR_REWRITE3;
}

br_status date_rewriter::mk_date_cmp(date_op_kind k, expr* d1, expr* d2, expr_ref& result) {
    // normalize gt/ge to lt/le
    if (k == OP_DATE_GT || k == OP_DATE_GE) {
        expr* args[2] = { d2, d1 };
        result = m.mk_app(get_fid(), k == OP_DATE_GT ? OP_DATE_LT : OP_DATE_LE, 2, args);
        return BR_REWRITE1;
    }
    if (d1 == d2) {
        result = m.mk_bool_val(k == OP_DATE_LE);
        return BR_DONE;
    }
    rational z1, z2;
    if (date_epoch_value(d1, z1) && date_epoch_value(d2, z2)) {
        result = m.mk_bool_val(k == OP_DATE_LT ? z1 < z2 : z1 <= z2);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status date_rewriter::mk_date_epoch(expr* d, expr_ref& result) {
    rational z;
    if (!date_epoch_value(d, z))
        return BR_FAILED;
    result = m_util.arith().mk_int(z);
    return BR_DONE;
}
