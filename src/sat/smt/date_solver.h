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

        date_util              u;
        th_rewriter            m_rw;
        svector<var_rep>       m_var2rep;
        expr_ref_vector        m_trail;
        ptr_vector<enode>      m_axiom_queue; // enodes whose defining axioms are pending
        unsigned               m_qhead = 0;
        rational               m_next_fresh;  // epoch numbers for unconstrained dates in models

        euf::theory_var mk_var(enode* n) override;
        void ensure_rep(enode* n);
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
