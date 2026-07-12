/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    calendar_rewriter.h

Abstract:

    Rewriting (definitional expansion) of calendar date operators into
    integer arithmetic.  See calendar_decl_plugin.h for the intended
    semantics and calendar_rewriter.cpp for the expansions.

Author:

    Claude (Anthropic) 2026-07-12

--*/
#pragma once

#include "ast/calendar_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"

class calendar_rewriter {
    ast_manager&   m;
    calendar_util  m_util;
    arith_util     m_arith;

    expr * mk_num(int n) { return m_arith.mk_int(n); }
    expr * mk_div(expr* a, int b) { return m_arith.mk_idiv(a, mk_num(b)); }
    expr * mk_mod(expr* a, int b) { return m_arith.mk_mod(a, mk_num(b)); }

    expr_ref mk_is_leap_year(expr* y);
    expr_ref mk_days_in_month(expr* y, expr* mo);
    expr_ref mk_valid(expr* y, expr* mo, expr* d);
    expr_ref mk_to_epoch(expr* y, expr* mo, expr* d);
    void mk_civil_parts(expr* n, expr_ref& year, expr_ref& month, expr_ref& day);
    expr_ref mk_day_of_week(expr* n);

public:
    calendar_rewriter(ast_manager & m): m(m), m_util(m), m_arith(m) {}
    family_id get_fid() const { return m_util.get_family_id(); }

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
};
