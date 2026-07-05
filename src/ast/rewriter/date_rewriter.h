/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.h

Abstract:

    Basic rewriting rules for the theory of calendar dates.

Author:

    Date theory extension 2026-07-05

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/params.h"

/**
   \brief Rewriting rules for date terms:
   - concrete evaluation of selectors, arithmetic and comparisons over
     calendar-valid numeral triples;
   - date.sub(d, py, pm, pd) --> date.add(d, -py, -pm, -pd);
   - comparisons --> lexicographic integer comparisons over selectors.
*/
class date_rewriter {
    ast_manager& m;
    date_util    m_util;
    arith_util   m_arith;

    br_status mk_selector(decl_kind k, expr* d, expr_ref& result);
    br_status mk_add(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);
    br_status mk_sub(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);
    br_status mk_cmp(decl_kind k, expr* a, expr* b, expr_ref& result);

    expr* mk_lex_lt(expr* a, expr* b, bool strict);

public:
    date_rewriter(ast_manager& m): m(m), m_util(m), m_arith(m) {}

    family_id get_fid() const { return m_util.get_family_id(); }

    date_util& u() { return m_util; }

    br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result);
};
