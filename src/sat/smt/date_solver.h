/*++
Copyright (c) 2026 CMU PASTA Lab

Module Name:

    date_solver.h

Abstract:

    Theory solver plugin for the Date sort (SAT/EUF core).

Author:

    Angel Cui

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "ast/date_decl_plugin.h"

namespace euf {
    class solver;
}

namespace date {

    class solver : public euf::th_euf_solver {
        typedef euf::theory_var theory_var;
        typedef euf::theory_id  theory_id;
        typedef euf::enode      enode;
        typedef sat::bool_var   bool_var;
        typedef sat::literal    literal;
        typedef sat::literal_vector literal_vector;

        date_util  m_util;
        arith_util m_autil;

        // Track which Date terms have had axioms injected
        obj_hashtable<expr> m_processed;
        // ---- axiom injection ----
        void inject_date_axioms(expr* e);
        void inject_mk_axioms(app* mk_term);
        void inject_cmp_axioms(app* atom);
        void inject_add_axioms(app* add_term);
        void inject_sub_axioms(app* sub_term);

        // ---- expression builders ----
        expr_ref mk_is_leap(expr* y);
        expr_ref mk_days_in_month(expr* y, expr* mo);

        // ---- concrete date arithmetic ----
        static int64_t floor_div(int64_t a, int64_t b);
        static int64_t floor_mod(int64_t a, int64_t b);
        static int64_t days_in_month_concrete(int64_t y, int64_t m);
        static bool compute_date_add(int64_t y, int64_t m, int64_t d,
                                     int64_t py, int64_t pm, int64_t pd,
                                     int64_t& ry, int64_t& rm, int64_t& rd);

        // ---- helpers ----
        void assert_eq(expr* a, expr* b);
        void assert_formula(expr* f);

    public:
        solver(euf::solver& ctx, theory_id id);

        // Required th_euf_solver interface
        bool is_external(bool_var v) override { return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx,
                             literal_vector& r, bool probing) override {}
        void asserted(literal l) override {}
        sat::check_result check() override { return sat::check_result::CR_DONE; }

        std::ostream& display(std::ostream& out) const override { return out; }
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override {
            return euf::th_explain::from_index(idx).display(out);
        }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override {
            return display_justification(out, idx);
        }
        void collect_statistics(statistics& st) const override {}
        euf::th_solver* clone(euf::solver& ctx) override;
        void new_eq_eh(euf::th_eq const& eq) override {}
        bool unit_propagate() override { return false; }

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;
        bool include_func_interp(func_decl* f) const override;

        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;

        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override;
        bool is_shared(theory_var v) const override { return false; }
    };

} // namespace date
