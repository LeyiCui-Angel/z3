/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory solver for calendar dates.

    The theory is solved by reduction to linear integer arithmetic.
    For every Date term t the solver asserts that the selector triple
    (date.year t, date.month t, date.day t) is a calendar-valid
    Gregorian date and that t is reconstructed from its selectors,
    t = (date.mk (date.year t) (date.month t) (date.day t)).
    Constructor, arithmetic and comparison operators are axiomatized
    over the selector triples; date.add and date.sub use the Rata Die
    day numbering, for which the day-carry loop of the specification
    is a plain shift.

Author:

    Angel Cui 2026-03-23

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_date : public theory {
        date_util       u;
        arith_util      a;
        th_rewriter     m_rw;
        expr_ref_vector m_values_trail;

        theory_var mk_var(enode* n) override;
        void assert_axiom(expr* e);
        void assert_implies(expr* premise, expr* conseq);
        void assert_iff(literal lit, expr* def);
        void add_date_axioms(enode* n);
        void add_mk_axioms(app* term);
        void add_arith_axioms(app* term, bool is_sub);
        expr_ref mk_lex_cmp(expr* x, expr* y, bool strict);
        expr_ref mk_rata_die(expr* d);
        expr* mk_neg(expr* e);

    public:
        theory_date(context& ctx);

        theory* mk_fresh(context* new_ctx) override { return alloc(theory_date, *new_ctx); }
        void init_model(model_generator& mg) override;
        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        final_check_status final_check_eh(unsigned) override { return FC_DONE; }
        model_value_proc* mk_value(enode* n, model_generator& mg) override;
        void display(std::ostream& out) const override;
        char const* get_name() const override { return "date"; }
    };

}
