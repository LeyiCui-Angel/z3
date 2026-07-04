/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.h

Abstract:

    Basic rewriting rules for the theory of calendar dates:
    concrete evaluation of selectors, arithmetic and comparisons
    over calendar-valid concrete dates.

Author:

    Claude (Anthropic) 2026-07-04

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"

class date_rewriter {
    date_util m_util;

    br_status mk_selector(decl_kind k, expr* d, expr_ref& result);
    br_status mk_add_sub(bool sub, expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);
    br_status mk_cmp(decl_kind k, expr* a, expr* b, expr_ref& result);

public:
    date_rewriter(ast_manager& m): m_util(m) {}

    ast_manager& m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }
    date_util& u() { return m_util; }

    br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result);
};
