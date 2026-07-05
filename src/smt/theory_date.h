/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory solver for calendar dates (legacy SMT pipeline).

    The solver works by reduction to integer arithmetic. Every Date
    term t is characterized by the integer triple
    (date.year t, date.month t, date.day t) and the theory asserts:

    - the triple of every Date term is a calendar-valid Gregorian date;
    - the reconstruction identity
      t = (date.mk (date.year t) (date.month t) (date.day t));
    - selectors invert date.mk on calendar-valid arguments;
    - date.add/date.sub shift the Rata Die day number of the
      month-normalized, end-of-month-clamped input;
    - comparisons are lexicographic on the triples;
    - for pairs of Date terms, equality and lexicographic order agree
      with equality and order of Rata Die day numbers.

    The integer reasoning is then discharged by the arithmetic solver.

Author:

    Claude 2026-07-05

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/date_rewriter.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_date : public theory {
        date_util       dt;
        arith_util      a;
        date_axioms     ax;

        // Lazily asserted axiom instantiations. The vector grows
        // monotonically; only the queue head is trailed, so axioms are
        // re-asserted when the solver backtracks past their creation.
        expr_ref_vector m_axioms;
        unsigned        m_axioms_qhead = 0;

        // Date terms seen so far, for pairwise order/equality bridges.
        expr_ref_vector m_dates;
        obj_hashtable<expr> m_seen;

        class date_value_proc;

        ast_manager& m() const { return get_manager(); }

        void push_axiom(expr* e);
        void add_date_term(app* term);
        enode* ensure_enode(app* term);

    public:
        theory_date(context& ctx);

        char const* get_name() const override { return "date"; }

        theory* mk_fresh(context* new_ctx) override { return alloc(theory_date, *new_ctx); }

        bool internalize_atom(app* atom, bool gate_ctx) override;

        bool internalize_term(app* term) override;

        void apply_sort_cnstr(enode* n, sort* s) override;

        void new_eq_eh(theory_var v1, theory_var v2) override {}

        void new_diseq_eh(theory_var v1, theory_var v2) override {}

        bool can_propagate() override;

        void propagate() override;

        void init_model(model_generator& mg) override;

        model_value_proc* mk_value(enode* n, model_generator& mg) override;

        void display(std::ostream& out) const override;
    };

    theory* mk_theory_date(context& ctx);
}
