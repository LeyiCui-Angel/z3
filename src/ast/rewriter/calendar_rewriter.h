/*++
Copyright (c) 2026 Theoria contributors

Module Name:

    calendar_rewriter.h

Abstract:

    Rewriting rules for the theory of calendar dates.

    Every calendar operator is eliminated by expanding it into an
    equivalent linear-integer-arithmetic term over its arguments
    (integer division and modulus by positive numeric constants,
    plus if-then-else).  The expansion is definitional: it introduces
    no fresh symbols and no side conditions, so it preserves
    satisfiability and models exactly.

Author:

    Claude (Theoria) 2026-07-12

--*/
#pragma once

#include "ast/calendar_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"

class calendar_rewriter {
    ast_manager&  m;
    calendar_util m_util;
    arith_util    m_arith;

    expr * mk_int(int i) { return m_arith.mk_int(i); }
    expr * mk_div(expr * x, int c);
    expr * mk_mod(expr * x, int c);
    expr * mk_epoch(expr * y, expr * mo, expr * d);
    void   mk_civil(expr * e, expr_ref & y, expr_ref & mo, expr_ref & d);
    expr * mk_leap(expr * y);
    expr * mk_days_in_month(expr * y, expr * mo);
public:
    calendar_rewriter(ast_manager & m): m(m), m_util(m), m_arith(m) {}
    family_id get_fid() const { return m_util.get_family_id(); }
    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
};
