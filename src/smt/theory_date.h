/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory solver for calendar dates.

    The solver reduces date constraints to linear integer arithmetic:
    every term x of sort Date is associated with the selector terms
    (date.year x), (date.month x), (date.day x), which are constrained
    to form a calendar-valid Gregorian triple, to reconstruct x through
    date.mk, and to round-trip through the epoch-day bijection.
    date.add / date.sub and the comparisons are compiled into epoch-day
    arithmetic over the selector triples.

Author:

    Date theory extension 2026-07-05

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "smt/smt_theory.h"
#include "model/value_factory.h"

namespace smt {

    class date_factory;

    class theory_date : public theory {
        date_util               m_util;
        th_rewriter             m_rewrite;
        // pending axioms: an entry with null m_atoms[i] asserts formula
        // m_rhs[i]; otherwise it asserts the equivalence m_atoms[i] <=> m_rhs[i]
        expr_ref_vector         m_atoms;
        expr_ref_vector         m_rhs;
        unsigned                m_qhead = 0;
        obj_hashtable<expr>     m_op_axiomatized;   // operator terms/atoms with instantiated axioms
        obj_hashtable<expr>     m_term_axiomatized; // date terms with validity/reconstruction axioms
        obj_hashtable<expr>     m_linked;           // terms linked to their rewriter normal form
        obj_hashtable<expr>     m_generated;        // reconstruction terms exempt from axioms
        expr_ref_vector         m_generated_refs;
        date_factory*           m_factory = nullptr;

        theory_var mk_th_var(enode* n);
        void queue_axiom(expr* e);
        void queue_no_rewrite(expr* e);
        void queue_equiv(expr* atom, expr* rhs);
        void assert_axiom(expr* atom, expr* rhs);
        void add_date_term_axioms(expr* e);
        bool link_normal_form(expr* e);
        literal mk_literal(expr* e);

    public:
        theory_date(context& ctx);

        char const * get_name() const override { return "date"; }

        theory * mk_fresh(context * new_ctx) override { return alloc(theory_date, *new_ctx); }

        bool internalize_atom(app * atom, bool gate_ctx) override;

        bool internalize_term(app * term) override;

        void apply_sort_cnstr(enode * n, sort * s) override;

        void new_eq_eh(theory_var v1, theory_var v2) override {}

        void new_diseq_eh(theory_var v1, theory_var v2) override;

        bool can_propagate() override { return m_qhead < m_rhs.size(); }

        void propagate() override;

        final_check_status final_check_eh(unsigned level) override {
            return can_propagate() ? FC_CONTINUE : FC_DONE;
        }

        void display(std::ostream & out) const override;

        void init_model(model_generator & mg) override;

        model_value_proc * mk_value(enode * n, model_generator & mg) override;

        // date.mk0 (the unspecified-constructor fallback) is treated as an
        // uninterpreted function; models record its interpretation so that
        // terms mentioning it evaluate consistently
        bool include_func_interp(func_decl* f) override {
            return is_decl_of(f, get_family_id(), OP_DATE_MK0);
        }
    };

}
