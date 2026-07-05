/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.h

Abstract:

    Basic rewriting rules for the theory of calendar dates.

    Provides concrete evaluation fast-paths: selectors applied to valid
    numeral constructors, date arithmetic on concrete dates and periods,
    and comparisons between concrete dates. Applications of date.mk to
    invalid numeral triples are left untouched; their meaning is
    unspecified by the theory.

Author:

    Angel Cui 2026-03-23

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"

class date_rewriter {
    date_util m_util;

    br_status mk_selector(date_op_kind k, expr* d, expr_ref& result);
    br_status mk_add(expr* d, expr* py, expr* pm, expr* pd, bool sign, expr_ref& result);
    br_status mk_cmp(date_op_kind k, expr* a, expr* b, expr_ref& result);

public:
    date_rewriter(ast_manager& m): m_util(m) {}

    ast_manager& m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }
    date_util& u() { return m_util; }

    br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result);
};
