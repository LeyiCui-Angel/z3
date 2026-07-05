/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.h

Abstract:

    Basic rewriting rules for dates.

Author:

    Date theory extension 2026-07-05

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"

/**
   \brief Cheap simplification rules for date terms:
   concrete evaluation of selectors, arithmetic and comparisons on
   calendar-valid concrete dates, and normalization of date.sub into
   date.add and of date.gt / date.ge into date.lt / date.le.
*/
class date_rewriter {
    date_util m_util;

    br_status mk_selector(decl_kind k, expr* arg, expr_ref& result);
    br_status mk_add(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);
    br_status mk_sub(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);
    br_status mk_compare(decl_kind k, expr* a, expr* b, expr_ref& result);

public:
    date_rewriter(ast_manager& m) : m_util(m) {}

    ast_manager& m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }
    date_util& u() { return m_util; }

    br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result);
};
