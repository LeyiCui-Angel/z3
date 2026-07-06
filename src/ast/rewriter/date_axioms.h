/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_axioms.h

Abstract:

    Axiomatization of the Dates theory into linear integer arithmetic.

    The encoding associates with every Date term t the selector terms
    (date.year t), (date.month t), (date.day t) and constrains them as
    follows:

    - validity:        1 <= month(t) <= 12,
                       1 <= day(t) <= days_in_month(year(t), month(t))
    - reconstruction:  t = (date.mk (date.year t) (date.month t) (date.day t))
                       for terms that are not date.mk applications
    - constructor:     every (date.mk y m d) occurrence carries the
                       implicit validity obligation of the DateSAT
                       front-end (Dates.smt2, :notes): (y, m, d) is
                       asserted calendar-valid and the selectors return
                       the arguments. Over concrete arguments the
                       obligation folds to true or false.
    - arithmetic:      date.add/date.sub are defined through the epoch-day
                       bijection between calendar-valid dates and integers
                       (days_from_civil / civil_from_days, using only
                       divisions by integer constants)
    - comparisons:     lexicographic order over the selector triples and,
                       equivalently, order over epoch days

    The axioms are shared by the legacy SMT solver (smt::theory_date) and
    the SAT/EUF solver (dates::solver).

Author:

    Date theory extension 2026-07-04

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/date_decl_plugin.h"
#include <functional>

namespace dates {

    class axioms {
        ast_manager&                      m;
        date_util                         dt;
        arith_util                        a;
        std::function<void(expr*)>        m_add_axiom;
        std::function<void(expr*, expr*)> m_add_eq;
        std::function<void(expr*, expr*)> m_add_iff;

        expr* mk_num(int k) { return a.mk_int(k); }

        expr_ref mk_neg(expr* e);

        void add_axiom(expr* e) { m_add_axiom(e); }
        void add_eq(expr* a, expr* b) { m_add_eq(a, b); }
        void add_iff(expr* atom, expr* def) { m_add_iff(atom, def); }

        void validity_axiom(expr* t);
        void epoch_roundtrip_axiom(expr* t);
        void reconstruction_axiom(expr* t);
        void constructor_axioms(app* t);
        void add_op_axioms(app* t, bool subtract);

    public:
        axioms(ast_manager& m);

        // add_axiom asserts a formula; the owner is expected to normalize
        // it (th_rewriter) before internalization.
        void set_add_axiom(std::function<void(expr*)> f) { m_add_axiom = std::move(f); }

        // add_eq asserts an equality whose sides must be internalized
        // verbatim: the left-hand side anchors selector and epoch terms
        // of the e-graph node being defined, so it must not be rewritten
        // (concrete evaluation would fold it away).
        void set_add_eq(std::function<void(expr*, expr*)> f) { m_add_eq = std::move(f); }

        // add_iff defines a comparison atom; the atom side must be kept
        // verbatim, the definition side may be normalized.
        void set_add_iff(std::function<void(expr*, expr*)> f) { m_add_iff = std::move(f); }

        date_util& u() { return dt; }

        // emit defining axioms for a term of sort Date
        void term_axioms(expr* t);

        // collect the implicit validity obligations of the DateSAT
        // front-end: one obligation per (date.mk y m d) occurrence in
        // fml, requiring (y, m, d) to be calendar-valid. Occurrences
        // under quantifiers are not visited. Used at assertion level so
        // the obligations survive preprocessing (e.g. solve-eqs
        // eliminating the only variable equated to a date.mk term).
        void collect_obligations(expr* fml, expr_ref_vector& obligations);

        // emit defining axioms for a comparison atom date.lt/le/gt/ge
        void compare_axioms(app* atom);

        // dates are determined by their selector triple: t1 != t2 implies
        // some selector differs. Instantiated on disequalities.
        void diseq_axiom(expr* t1, expr* t2);

        // (or (and (= (mod y 4) 0) (not (= (mod y 100) 0))) (= (mod y 400) 0))
        expr_ref mk_is_leap(expr* y);

        // number of days of month mo in year y as an if-then-else term
        expr_ref mk_days_in_month(expr* y, expr* mo);

        // (y, mo, d) is a calendar-valid Gregorian date
        expr_ref mk_valid_triple(expr* y, expr* mo, expr* d);

        // number of days since 1970-01-01 of the valid date (y, mo, d);
        // only divisions by positive integer constants are used
        expr_ref mk_days_from_civil(expr* y, expr* mo, expr* d);

        // inverse of mk_days_from_civil: valid date (y, mo, d) of an epoch day
        void mk_civil_from_days(expr* e, expr_ref& y, expr_ref& mo, expr_ref& d);

        // epoch day of a Date term, days_from_civil over its selectors
        expr_ref mk_epoch(expr* t);
    };
}
