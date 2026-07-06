/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.h

Abstract:

    Basic rewriting rules for date terms.

    - date.sub is normalized to date.add with negated period arguments.
    - date.gt/date.ge are normalized to date.lt/date.le with swapped arguments.
    - Selectors, arithmetic and comparisons over concrete calendar-valid
      dates are evaluated. Applications of date.mk to invalid concrete
      triples fold to the fixed total interpretation (date_util::normalize_mk),
      refining their intentionally unspecified value deterministically so that
      simplification, theory solvers and model evaluation agree.

Author:

    Claude 2026-07-04

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/params.h"

/**
   \brief Cheap rewrite rules for date terms
*/
class date_rewriter {
    ast_manager& m;
    date_util    m_util;

    br_status mk_date_mk(expr* y, expr* mo, expr* d, expr_ref& result);

    br_status mk_date_selector(decl_kind k, expr* a, expr_ref& result);

    br_status mk_date_add(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);

    br_status mk_date_sub(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);

    br_status mk_date_cmp(decl_kind k, expr* a, expr* b, expr_ref& result);

public:

    date_rewriter(ast_manager& m, params_ref const& p = params_ref()):
        m(m), m_util(m) {}

    family_id get_fid() const { return m_util.get_family_id(); }

    void updt_params(params_ref const& p) {}

    static void get_param_descrs(param_descrs& r) {}

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    expr_ref mk_app(func_decl* f, expr_ref_vector const& args) { return mk_app(f, args.size(), args.data()); }

    expr_ref mk_app(func_decl* f, unsigned n, expr* const* args) {
        expr_ref result(m);
        if (f->get_family_id() != get_fid() ||
            BR_FAILED == mk_app_core(f, n, args, result))
            result = m.mk_app(f, n, args);
        return result;
    }
};
