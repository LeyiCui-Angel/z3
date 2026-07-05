/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.h

Abstract:

    Basic rewriting rules for the theory of calendar dates, together
    with the shared axiom builder used by both theory solvers.

    The rewriter only evaluates applications whose semantics the theory
    actually specifies: date.mk applications on calendar-invalid numeral
    triples are deliberately left untouched.

Author:

    Claude 2026-07-05

--*/
#pragma once

#include "ast/ast.h"
#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"

class date_rewriter {
    ast_manager& m;
    date_util    m_util;
    arith_util   m_arith;

    br_status mk_date_add(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);
    br_status mk_date_sub(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result);
    br_status mk_date_selector(decl_kind k, expr* d, expr_ref& result);
    br_status mk_date_cmp(decl_kind k, expr* d1, expr* d2, expr_ref& result);

public:
    date_rewriter(ast_manager& m):
        m(m), m_util(m), m_arith(m) {}

    family_id get_fid() const { return m_util.get_family_id(); }

    br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result);
};

/**
   \brief Builder for the arithmetic reduction of date constraints.

   Every Date term t is characterized by the integer triple
   (date.year t, date.month t, date.day t). The formulas produced here
   axiomatize the theory over that triple:

   - valid_axiom:  the triple of any Date term is a calendar-valid date;
   - recon_axiom:  t = (date.mk (date.year t) (date.month t) (date.day t));
   - mk_axiom:     selectors invert date.mk on calendar-valid arguments;
   - add_axiom:    the Rata Die day number of the result of date.add
                   equals the day number of the month-normalized and
                   end-of-month-clamped input, shifted by the day offset;
   - cmp_axiom:    comparisons are lexicographic on the triples;
   - bridge_axiom: equality and order on two Date terms agree with
                   equality and order of their Rata Die day numbers.
*/
class date_axioms {
    ast_manager& m;
    date_util    dt;
    arith_util   a;

    expr* mk_int(int i) { return a.mk_int(i); }

    // Inequality atoms are built in the normalized form expected by the
    // arithmetic solvers (linear term compared against a numeral): the
    // axioms are asserted without a rewriting pass.
    expr* mk_le_atom(expr* x, expr* y);
    expr* mk_lt_atom(expr* x, expr* y);

public:
    date_axioms(ast_manager& m):
        m(m), dt(m), a(m) {}

    expr_ref mk_is_leap_year(expr* y);
    expr_ref mk_days_in_month(expr* y, expr* mo);
    expr_ref mk_is_valid(expr* y, expr* mo, expr* d);
    expr_ref mk_rata_die(expr* y, expr* mo, expr* d);
    expr_ref mk_rata_die(expr* d);
    expr_ref mk_lex_lt(expr* d1, expr* d2, bool strict);

    expr_ref valid_axiom(expr* t);
    expr_ref recon_axiom(expr* t);
    expr_ref mk_axiom(app* c);
    expr_ref add_axiom(app* e);
    expr_ref cmp_axiom(app* atom);
    expr_ref bridge_axiom(expr* t, expr* u);
};
