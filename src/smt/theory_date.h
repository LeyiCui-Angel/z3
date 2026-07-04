/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory plugin for calendar dates.

    The theory reduces date constraints to integer arithmetic:

    - Every Date term x is associated with the selector terms
      (date.year x), (date.month x), (date.day x), which are constrained
      to form a calendar-valid Gregorian date, and x is identified with
      the reconstruction (date.mk (date.year x) (date.month x) (date.day x)).

    - For (date.mk y m d), the selector equations
      date.year(date.mk y m d) = y, etc., are guarded by calendar
      validity of the triple (y, m, d); invalid constructor applications
      denote an unspecified (but valid) date.

    - (date.add d py pm pd) is characterized by an equation over the
      day-number (rata die) bijection between valid dates and integers:
      rata_die(add) = rata_die(month-normalized, EOM-clamped d) + pd.
      date.sub is date.add with negated period arguments.

    - Comparisons are mapped to integer comparisons of day numbers,
      which agree with the lexicographic order on (year, month, day)
      for calendar-valid dates.

Author:

    Claude 2026-07-04

--*/
#pragma once

#include "smt/smt_theory.h"
#include "ast/date_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"

namespace smt {

    class theory_date : public theory {
        date_util        u;
        th_rewriter      m_rw;
        // selector terms per theory variable; used for model construction
        ptr_vector<app>  m_year;
        ptr_vector<app>  m_month;
        ptr_vector<app>  m_day;

        theory_var mk_th_var(enode* n);
        void ensure_date_axioms(enode* n);
        // simplify e and assert it as a theory axiom; simplification keeps
        // the arithmetic solver on its linear fragment and evaluates the
        // calendar functions on concrete dates
        void assert_axiom(expr* e);
        void add_mk_axioms(app* t);
        void add_arith_axioms(app* t);
        void add_cmp_axioms(literal lit, app* atom);

        app* year_of(theory_var v) const { return m_year[v]; }
        app* month_of(theory_var v) const { return m_month[v]; }
        app* day_of(theory_var v) const { return m_day[v]; }

    public:
        theory_date(context& ctx);

        char const * get_name() const override { return "date"; }

        theory * mk_fresh(context * new_ctx) override { return alloc(theory_date, *new_ctx); }

        bool internalize_atom(app * atom, bool gate_ctx) override;

        bool internalize_term(app * term) override;

        void apply_sort_cnstr(enode * n, sort * s) override;

        void new_eq_eh(theory_var v1, theory_var v2) override {}

        void new_diseq_eh(theory_var v1, theory_var v2) override {}

        final_check_status final_check_eh(unsigned) override { return FC_DONE; }

        void init_model(model_generator & mg) override;

        model_value_proc * mk_value(enode * n, model_generator & mg) override;

        void display(std::ostream & out) const override;
    };

}
