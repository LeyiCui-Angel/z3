/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Legacy-SMT theory solver for the native theory of calendar dates.

    The solver is a lazy reduction theory: whenever a Date term or a date
    comparison atom is internalized it asks date_axiom_gen for the defining
    axioms (over the integer projections date.year / date.month / date.day)
    and asserts them into the smt::context, delegating all reasoning to the
    arithmetic + EUF core.

    See ast/date_axioms.h and Dates.smt2 for the specification.

Author:

    Angel Cui 2026

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/date_axioms.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_date : public theory {
        date_util           du;
        arith_util          a;
        date_axiom_gen      m_gen;
        th_rewriter         m_rw;          // normalize the reduced arithmetic
        obj_hashtable<expr> m_processed;   // date terms/atoms already reduced
        expr_ref_vector     m_axioms;      // reduced axioms pending assertion

        theory_var mk_var(enode* n) override;

        // Axioms are buffered while a term is being reduced and asserted only
        // once it is fully built: rewriting mid-construction would run while
        // raw, unreferenced intermediate terms are still live.  Injecting the
        // rewritten formulas via mk_th_axiom keeps theory_arith / theory_lra
        // from reporting spurious incompleteness (they need the normalized
        // form the rewriter produces).
        void emit_date_axioms(expr* t);
        void internalize_predicate(app* atom);
        void flush_axioms();

    public:
        theory_date(context& ctx);

        theory* mk_fresh(context* new_ctx) override { return alloc(theory_date, *new_ctx); }
        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        void display(std::ostream& out) const override {}
        model_value_proc* mk_value(enode* n, model_generator& mg) override;
        void init_model(model_generator& mg) override;
        char const* get_name() const override { return "date"; }
    };

}
