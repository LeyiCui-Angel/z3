/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_axioms.h

Abstract:

    Axiomatization of the theory of calendar dates over linear integer
    arithmetic. Shared between the legacy SMT solver (smt::theory_date)
    and the SAT/EUF solver (date::solver).

    For every term d of sort Date:

    - validity:       1 <= date.month(d) <= 12,
                      1 <= date.day(d) <= days_in_month(year, month)
                      (with the Gregorian leap year rule for February);
    - reconstruction: d = date.mk(date.year(d), date.month(d), date.day(d))
                      (instantiated for non-constructor terms; for
                      constructor terms it follows from the guarded
                      selector axioms and congruence).

    For constructor terms (date.mk y m d):

    - guarded selectors: if (y, m, d) is calendar-valid then
                      date.year(date.mk y m d) = y, etc.

    For (date.add d py pm pd) (and date.sub with negated offsets),
    following the three-step algorithm of the theory specification:

    - month normalization and end-of-month clamp are encoded directly;
    - the day carry is encoded through the rata-die bijection
      days_from_civil between calendar-valid dates and integers:
          days_from_civil(result) =
              days_from_civil(normalized-and-clamped date) + pd.
      Together with the validity axioms on the result this pins the
      result down uniquely in linear integer arithmetic.

    Comparison atoms unfold to the lexicographic order on selectors.

Author:

    Date theory extension 2026-07-05

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include <functional>

class date_axioms {
public:
    // a clause is a disjunction of the given (boolean expression) literals
    typedef std::function<void(expr_ref_vector const&)> clause_sink;

private:
    ast_manager& m;
    date_util    u;
    arith_util   a;
    clause_sink  m_add_clause;

    expr* mk_int(int k) { return a.mk_int(rational(k)); }
    expr* mk_leap(expr* y);
    expr* mk_clamp_day(expr* y, expr* mo, expr* d);
    expr* mk_valid(expr* y, expr* mo, expr* d);
    expr* mk_days_from_civil(expr* y, expr* mo, expr* d);

    void add_clause(expr* l1, expr* l2 = nullptr, expr* l3 = nullptr);

public:
    date_axioms(ast_manager& m, clause_sink add_clause):
        m(m), u(m), a(m), m_add_clause(add_clause) {}

    /**
       \brief Validity and reconstruction axioms for a term of sort Date.
    */
    void date_term_axioms(expr* d);

    /**
       \brief Guarded selector axioms for a (date.mk y m d) term.
    */
    void mk_axioms(app* e);

    /**
       \brief Defining axiom for (date.add d py pm pd); handles date.sub
       by negating the period arguments.
    */
    void add_axioms(app* e);

    /**
       \brief Defining axioms for a comparison atom (two clauses relating
       the atom to its lexicographic expansion).
    */
    void cmp_axioms(app* e);

    /**
       \brief Lexicographic order on the selector triples.
    */
    expr_ref mk_lex_lt(expr* d1, expr* d2, bool strict);
};
