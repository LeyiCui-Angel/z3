/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.h

Abstract:

    Rewriting rules for date terms: constant folding of the calendar
    operations over valid date values, and reduction of
    date.gt/date.ge/date.sub to date.lt/date.le/date.add.

Author:

    Z3 date theory extension 2026-07-05

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/params.h"

class date_rewriter {
    ast_manager& m;
    date_util    m_util;

    br_status mk_date_mk(expr* y, expr* mo, expr* d, expr_ref& result);
    br_status mk_date_selector(date_op_kind k, expr* d, expr_ref& result);
    br_status mk_date_add(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);
    br_status mk_date_sub(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);
    br_status mk_date_cmp(date_op_kind k, expr* d1, expr* d2, expr_ref& result);
    br_status mk_date_epoch(expr* d, expr_ref& result);

    bool date_epoch_value(expr* e, rational& z) const;

public:
    date_rewriter(ast_manager& m): m(m), m_util(m) {}

    family_id get_fid() const { return m_util.get_family_id(); }
    date_util& u() { return m_util; }

    br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result);

    expr_ref mk_app(func_decl* f, unsigned n, expr* const* args) {
        expr_ref result(m);
        if (f->get_family_id() != get_fid() ||
            BR_FAILED == mk_app_core(f, n, args, result))
            result = m.mk_app(f, n, args);
        return result;
    }
};
