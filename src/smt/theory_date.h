/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory solver for the Dates theory in the legacy SMT core.

    The solver reduces date constraints to linear integer arithmetic by
    instantiating the axioms from ast/rewriter/date_axioms.h for every
    internalized Date term and date comparison atom. Model values of
    sort Date are calendar-valid (date.mk y m d) applications assembled
    from the arithmetic model values of the selector terms.

Author:

    Date theory extension 2026-07-04

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/date_axioms.h"
#include "ast/rewriter/th_rewriter.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_date : public theory {
        date_util        dt;
        arith_util       a;
        dates::axioms    m_ax;
        th_rewriter      m_rw;
        ptr_vector<expr> m_terms;       // Date terms whose axioms are pending
        ptr_vector<app>  m_atoms;       // comparison atoms whose axioms are pending
        unsigned         m_terms_qhead = 0;
        unsigned         m_atoms_qhead = 0;

        void assert_axiom(expr* e);
        void assert_eq(expr* a, expr* b);
        void assert_iff(expr* atom, expr* def);
        void add_date_term(enode* n);
        bool flush_axioms();

    public:
        theory_date(context& ctx);

        theory * mk_fresh(context * new_ctx) override { return alloc(theory_date, *new_ctx); }
        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void apply_sort_cnstr(enode * n, sort * s) override;
        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        bool can_propagate() override;
        void propagate() override;
        final_check_status final_check_eh(unsigned level) override;
        void display(std::ostream& out) const override;
        model_value_proc * mk_value(enode * n, model_generator & mg) override;
    };
}
