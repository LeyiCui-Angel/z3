/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for the Dates theory in the SAT/EUF core.

    Like smt::theory_date, the solver reduces date constraints to linear
    integer arithmetic by instantiating the axioms from
    ast/rewriter/date_axioms.h for every internalized Date term and date
    comparison atom.

Author:

    Date theory extension 2026-07-04

--*/
#pragma once

#include "sat/smt/euf_solver.h"
#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/date_axioms.h"
#include "ast/rewriter/th_rewriter.h"

namespace dates {

    class solver : public euf::th_euf_solver {
        date_util        dt;
        arith_util       a;
        dates::axioms    m_ax;
        th_rewriter      m_rw;
        ptr_vector<expr> m_queue;       // terms and atoms whose axioms are pending
        svector<std::pair<euf::theory_var, euf::theory_var>> m_diseqs; // disequalities whose axioms are pending
        unsigned         m_qhead = 0;
        unsigned         m_dhead = 0;

        void assert_axiom(expr* e);
        void assert_eq(expr* a, expr* b);
        void assert_iff(expr* atom, expr* def);
        void push_queue(expr* e);
        void track(euf::enode* n);
        bool flush_axioms();

        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;

    public:
        solver(euf::solver& ctx);

        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override;

        void asserted(sat::literal l) override {}
        void new_eq_eh(euf::th_eq const& eq) override {}
        void new_diseq_eh(euf::th_eq const& eq) override;

        bool unit_propagate() override;
        sat::check_result check() override;
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override { UNREACHABLE(); }

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { UNREACHABLE(); return out; }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { UNREACHABLE(); return out; }

        euf::th_solver* clone(euf::solver& ctx) override { return alloc(solver, ctx); }
    };
}
