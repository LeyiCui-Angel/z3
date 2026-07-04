/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Legacy-SMT theory solver for the native theory of calendar dates.

    The solver is a lazy axiomatization / reduction theory: it does not
    perform its own propagation.  Whenever a Date term or a date predicate
    atom is internalized it injects helper axioms over integer arithmetic
    and Booleans into the smt::context and delegates all reasoning to the
    arithmetic + EUF core.

    See ast/date_decl_plugin.h and Dates.smt2 for the specification.

Author:

    Angel Cui 2026

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_date : public theory {
        date_util           du;
        arith_util          a;
        th_rewriter         m_rw;          // normalize injected arithmetic
        obj_hashtable<expr> m_processed;   // date terms whose axioms were emitted
        expr_ref_vector     m_axioms;      // reduction axioms pending assertion

        theory_var mk_var(enode* n) override;

        // axiom emission.  assert_axiom() only buffers the formula: the
        // helper builders assert their side constraints (div/mod definitions)
        // mid-construction, and running the rewriter then -- while raw,
        // unreferenced intermediate terms are still live -- would corrupt the
        // ast.  flush_axioms() rewrites and asserts the buffer once the term
        // is fully built, at the top of internalize_term / internalize_atom.
        void assert_axiom(expr* fml);
        void flush_axioms();
        void emit_date_axioms(expr* t);
        void emit_add_axioms(app* t, bool is_sub);
        void internalize_predicate(app* atom);

        // Euclidean div/mod by a positive constant, eliminated into fresh
        // linear integer variables so the reduction stays inside LIA (raw
        // div/mod terms injected at internalization make theory_arith
        // report incompleteness).
        void   mk_divmod(expr* x, int n, expr_ref& q, expr_ref& r);
        expr_ref mk_emod(expr* x, int n);
        expr_ref mk_ediv(expr* x, int n);

        // term-vs-term comparisons, written with 0 on one side
        expr* mk_le0(expr* x, expr* y);
        expr* mk_lt0(expr* x, expr* y);

        // calendar helper expressions
        expr_ref mk_is_leap(expr* y);
        expr_ref mk_days_in_month(expr* y, expr* m);
        expr_ref mk_min(expr* x, expr* y);
        expr_ref mk_valid(expr* y, expr* m, expr* d);
        expr_ref mk_serial(expr* y, expr* m, expr* d);
        expr_ref mk_lex_lt(expr* y1, expr* m1, expr* d1, expr* y2, expr* m2, expr* d2);

        expr* neg_offset(expr* e, bool is_sub);
        void  bind(expr_ref& e);
        // date.add month-normalization (step 1) and end-of-month clamp (step 2)
        void compute_norm(expr* d, expr* py, expr* pm,
                          expr_ref& oy, expr_ref& om, expr_ref& clamp);
        // date.add day carry (step 3), unfolded for a concrete offset k
        void day_carry(expr_ref& oy, expr_ref& om, expr_ref& tmp, int64_t k);

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
