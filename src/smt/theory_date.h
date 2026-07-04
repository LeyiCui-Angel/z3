/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory solver for calendar dates (legacy SMT core).

    The solver reduces the date operations to linear integer arithmetic
    over the selector terms (date.year t), (date.month t), (date.day t)
    of every term t of sort Date:

    - every date term is constrained to be calendar-valid;
    - date.mk, date.add, date.sub and the comparisons are axiomatized
      by the arithmetic definitions provided by date_util;
    - extensionality (dates with equal components are equal) is enforced
      lazily at final check, guided by the arithmetic model.

Author:

    Claude (Anthropic) 2026-07-04

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/date_factory.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_date : public theory {
        date_util           m_util;
        arith_util          m_arith;
        th_rewriter         m_rewrite;
        obj_hashtable<expr> m_axiomatized;
        ptr_vector<expr>    m_terms;       // axiomatized terms of sort Date
        date_factory*       m_factory { nullptr };

        date_util& u() { return m_util; }

        void ensure_axioms(expr* t);
        void assert_axiom(expr* fml);
        void internalize_cmp(literal lit, app* atom);
        bool get_component_values(expr* t, rational& y, rational& mo, rational& d);
        bool is_date(expr* t) const { return m_util.is_date(t->get_sort()); }

        theory_var mk_th_var(enode* n);

        friend class date_value_proc;

    public:
        theory_date(context& ctx);

        theory* mk_fresh(context* new_ctx) override { return alloc(theory_date, *new_ctx); }
        char const* get_name() const override { return "date"; }

        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        final_check_status final_check_eh(unsigned level) override;
        void display(std::ostream& out) const override;

        void init_model(model_generator& mg) override;
        model_value_proc* mk_value(enode* n, model_generator& mg) override;
    };

}
