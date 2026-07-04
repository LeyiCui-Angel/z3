/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_axioms.h

Abstract:

    Shared reduction of the native date theory to linear integer
    arithmetic + EUF.  Given a Date term or a date comparison atom it
    produces the set of defining axioms (over the integer projections
    date.year / date.month / date.day) that both the legacy SMT theory
    (theory_date) and the SAT/EUF solver (date_solver) assert into their
    respective cores.

    The generated axioms use only:
      * linear integer arithmetic (comparisons are written with 0 on one
        side; div/mod are eliminated into fresh variables);
      * if-then-else, capped behind fresh variables so the rewriter does
        not blow up when lifting equalities over nested ITEs;
      * the built-in equality over the Date sort (for reconstruction).

    See Dates.smt2 for the specification.

Author:

    Angel Cui 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/date_decl_plugin.h"

class date_axiom_gen {
    ast_manager&     m;
    arith_util       a;
    date_util        du;
    expr_ref_vector* m_out { nullptr };   // sink for the current reduction

    void push(expr* e) { m_out->push_back(e); }
    void bind(expr_ref& e);

    expr* mk_le0(expr* x, expr* y);       // x <= y
    expr* mk_lt0(expr* x, expr* y);       // x < y

    void     mk_divmod(expr* x, int n, expr_ref& q, expr_ref& r);
    expr_ref mk_emod(expr* x, int n);
    expr_ref mk_ediv(expr* x, int n);

    expr_ref mk_is_leap(expr* y);
    expr_ref mk_days_in_month(expr* y, expr* mo);
    expr_ref mk_min(expr* x, expr* y);
    expr_ref mk_valid(expr* y, expr* mo, expr* d);
    expr_ref mk_serial(expr* y, expr* mo, expr* d);
    expr_ref mk_lex_lt(expr* y1, expr* m1, expr* d1, expr* y2, expr* m2, expr* d2);

    expr* neg_offset(expr* e, bool is_sub);
    void  compute_norm(expr* d, expr* py, expr* pm, expr_ref& oy, expr_ref& om, expr_ref& clamp);
    void  day_carry(expr_ref& oy, expr_ref& om, expr_ref& tmp, int64_t k);
    void  emit_add_axioms(app* t, bool is_sub);

public:
    date_axiom_gen(ast_manager& m);

    date_util& util() { return du; }

    // Append to \c out the defining axioms of the Date-sorted term \c t.
    void reduce_term(expr* t, expr_ref_vector& out);

    // Append to \c out the definition (atom <=> lexicographic body) of a
    // date comparison atom (date.lt/le/gt/ge).
    void reduce_atom(app* atom, expr_ref_vector& out);
};
