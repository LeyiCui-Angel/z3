/*++
Copyright (c) 2026 CMU PASTA Lab

Module Name:

    theory_date.h

Abstract:

    SMT theory plugin for the Date sort (legacy SMT core).

    This theory injects axioms for:
      - Calendar validity of every Date term
      - Selector axioms for date.mk constructors
      - Comparison expansion (date.lt/le/gt/ge ↔ lex order on components)
      - Date arithmetic (date.add, date.sub)

Author:

    Angel Cui

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_date : public theory {
        date_util  m_util;
        arith_util m_autil;

        // Track which Date terms have had axioms injected to avoid duplicates
        obj_hashtable<expr> m_processed;

        // ---- axiom injection helpers ----

        // Inject validity + reconstruction for a Date term
        void inject_date_axioms(expr* e);

        // Inject selector axioms for a date.mk(y, m, d) term
        void inject_mk_axioms(app* mk_term);

        // Inject comparison expansion for a date comparison atom
        void inject_cmp_axioms(app* atom);

        // Inject arithmetic axioms for date.add(d, py, pm, pd)
        void inject_add_axioms(app* add_term);

        // Inject date.sub definition: date.sub(d,py,pm,pd) = date.add(d,-py,-pm,-pd)
        void inject_sub_axioms(app* sub_term);

        // ---- expression builders ----

        // Build ite expression for days_in_month(y, m)
        expr_ref mk_days_in_month(expr* y, expr* m);

        // Build is_leap(y) expression
        expr_ref mk_is_leap(expr* y);

        // Build lex_lt(d1, d2): the lexicographic strict-less-than expansion
        expr_ref mk_lex_lt(expr* d1, expr* d2);

        // Build absolute day count formula for a Date term
        expr_ref mk_abs_day(expr* d);

        // ---- concrete date arithmetic ----

        static int64_t floor_div(int64_t a, int64_t b);
        static int64_t floor_mod(int64_t a, int64_t b);
        static int64_t days_in_month_concrete(int64_t y, int64_t m);
        static bool compute_date_add(int64_t y, int64_t m, int64_t d,
                                     int64_t py, int64_t pm, int64_t pd,
                                     int64_t& ry, int64_t& rm, int64_t& rd);

        // ---- helpers ----
        void assert_unit(expr* formula);

    protected:
        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void new_eq_eh(theory_var v1, theory_var v2) override {}
        bool use_diseqs() const override { return false; }
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        void reset_eh() override;
        final_check_status final_check_eh(unsigned) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        void display(std::ostream& out) const override {}

    public:
        theory_date(context& ctx, ast_manager& m);

        theory* mk_fresh(context* new_ctx) override;
        char const* get_name() const override { return "date"; }
        bool build_models() const override { return true; }
        void add_theory_assumptions(expr_ref_vector& assumptions) override {}
    };

} // namespace smt
