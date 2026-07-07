/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for calendar dates (SAT/EUF core).
    See date_decl_plugin.h for the semantics of the theory and
    smt/theory_date.h for an overview of the epoch-based reduction to
    linear integer arithmetic; this solver implements the same
    axiomatization for the SAT/EUF pipeline.

Author:

    Angel Cui's date theory task 2026-07-04

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "sat/smt/sat_th.h"

namespace euf {
    class solver;
}

namespace dates {

    typedef euf::enode enode;
    typedef euf::theory_var theory_var;

    class solver : public euf::th_euf_solver {
        // epoch and civil component terms of a date-sorted theory variable
        struct var_rep {
            enode* m_epoch { nullptr };
            expr*  m_year { nullptr };
            expr*  m_month { nullptr };
            expr*  m_day { nullptr };
        };

        // Defining axioms of a date term, built once per expression and
        // never popped: theory variables and their axioms are replayed
        // after backtracking, and reusing the same constants and formulas
        // keeps the replayed axioms identical to the original ones.
        //
        // The axioms come in two layers. The epoch layer defines the
        // epoch day number of the term (as a numeral, an arithmetic
        // shift, or the month arithmetic of date.add/date.sub) and keeps
        // it inside [min_epoch(), max_epoch()], which is all that
        // comparisons, equalities and models need. The civil layer
        // introduces the (year, month, day) components together with the
        // epoch computation over them; it is materialized lazily, only
        // for terms whose components are actually referenced (selector
        // arguments, symbolic date.mk applications, and the first
        // argument of date.add/date.sub).
        struct rep_axioms {
            expr_ref        m_epoch_def;   // epoch value of the term
            expr_ref        m_epoch_def2;  // second epoch equation of date.add/date.sub terms
            expr_ref_vector m_epoch_fmls;
            expr_ref        m_year, m_month, m_day;
            expr_ref        m_civil_def;   // epoch computed from the components
            expr_ref_vector m_civil_fmls;
            rep_axioms(ast_manager& m):
                m_epoch_def(m), m_epoch_def2(m), m_epoch_fmls(m),
                m_year(m), m_month(m), m_day(m), m_civil_def(m), m_civil_fmls(m) {}
        };

        date_util              u;
        th_rewriter            m_rw;
        svector<var_rep>       m_var2rep;
        obj_map<expr, rep_axioms*> m_reps;
        expr_ref_vector        m_trail;
        ptr_vector<enode>      m_axiom_queue; // enodes whose defining axioms are pending
        svector<std::pair<expr*, expr*>> m_link_queue; // date pairs whose coupling axioms are pending
        unsigned               m_qhead = 0;
        unsigned               m_lhead = 0;
        rational               m_next_fresh;  // epoch numbers for unconstrained dates in models

        euf::theory_var mk_var(enode* n) override;
        void ensure_epoch(enode* n);
        void ensure_civil(enode* n);
        void set_civil(theory_var v, rep_axioms const& ra);
        rep_axioms& get_rep_axioms(app* t);
        void build_civil(app* t, rep_axioms& ra);
        void link_eq(expr* x, expr* y);
        void push_link(expr* x, expr* y);
        bool is_ground_valid_mk(app* t) const;
        enode* get_epoch(enode* n) const;
        void add_axiom(expr* e);
        void add_axioms(expr_ref_vector const& fmls);
        void add_axiom_eq(expr* lhs, expr* rhs);
        void axiomatize(enode* n);
        void push_axiom(enode* n);

        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;

    public:
        solver(euf::solver& ctx);
        ~solver() override;

        void asserted(sat::literal l) override {}
        sat::check_result check() override;
        bool unit_propagate() override;

        void new_eq_eh(euf::th_eq const& eq) override;
        bool use_diseqs() const override { return true; }
        void new_diseq_eh(euf::th_eq const& eq) override;

        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        void pop_core(unsigned num_scopes) override;

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return out; }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return out; }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override { UNREACHABLE(); }

        euf::th_solver* clone(euf::solver& ctx) override { return alloc(solver, ctx); }
    };

}
