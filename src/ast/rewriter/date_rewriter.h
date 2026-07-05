/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.h

Abstract:

    Rewriting (constant folding) rules for the theory of calendar dates.
    See date_decl_plugin.h for the semantics of the theory.

Author:

    Angel Cui's date theory task 2026-07-04

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"

/**
   \brief Cheap rewrite rules for date terms. Ground applications of all
   date operations are evaluated to values (normalized date.mk terms or
   numerals); date.gt/date.ge are normalized to date.lt/date.le.
*/
class date_rewriter {
    ast_manager& m;
    date_util    u;

    br_status mk_date_mk(expr* y, expr* mo, expr* d, expr_ref& result);
    br_status mk_date_selector(decl_kind k, expr* d, expr_ref& result);
    br_status mk_date_add(bool sub, expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);
    br_status mk_date_cmp(decl_kind k, expr* a, expr* b, expr_ref& result);
    br_status mk_date_epoch(expr* d, expr_ref& result);

public:
    date_rewriter(ast_manager& m) : m(m), u(m) {}

    family_id get_fid() const { return u.get_family_id(); }

    date_util& util() { return u; }

    br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result);
};
