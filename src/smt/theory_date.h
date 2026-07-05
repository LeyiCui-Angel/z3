/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory solver for calendar dates in the legacy SMT pipeline.

    The solver reduces date constraints to linear integer arithmetic by
    eagerly instantiating the axioms of date_axioms for every internalized
    date term: validity and reconstruction axioms for terms of sort Date,
    guarded selector axioms for constructor applications, the three-step
    calendar arithmetic algorithm for date.add/date.sub, and lexicographic
    definitions for comparison atoms.

Author:

    Date theory extension 2026-07-05

--*/
#pragma once

#include "smt/smt_theory.h"
#include "ast/date_decl_plugin.h"
#include "ast/rewriter/date_axioms.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/date_factory.h"

namespace smt {

    class theory_date : public theory {
        date_util           u;
        arith_util          a;
        th_rewriter         m_rw;
        date_axioms         m_ax;
        obj_hashtable<expr> m_axiomatized;
        date_factory*       m_factory { nullptr };

        void add_clause(expr_ref_vector const& lits);
        void ensure_axioms(expr* e);

    public:
        theory_date(context& ctx);

        char const* get_name() const override { return "date"; }

        theory * mk_fresh(context * new_ctx) override { return alloc(theory_date, *new_ctx); }

        bool internalize_atom(app * atom, bool gate_ctx) override;

        bool internalize_term(app * term) override;

        void apply_sort_cnstr(enode * n, sort * s) override;

        void new_eq_eh(theory_var v1, theory_var v2) override {}

        void new_diseq_eh(theory_var v1, theory_var v2) override {}

        void display(std::ostream & out) const override;

        void init_model(model_generator & mg) override;

        model_value_proc * mk_value(enode * n, model_generator & mg) override;
    };
}
