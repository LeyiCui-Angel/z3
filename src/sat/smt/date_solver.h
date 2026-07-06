/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for calendar dates for the SAT/EUF core.

    Mirrors smt::theory_date: date constraints are reduced to linear
    integer arithmetic over the selector triples of Date terms and
    their epoch-day images.

Author:

    Date theory extension 2026-07-05

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "sat/smt/sat_th.h"

namespace euf {
    class solver;
}

namespace date {

    class solver : public euf::th_euf_solver {
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

        void queue_axiom(expr* e);
        void queue_no_rewrite(expr* e);
        void queue_equiv(expr* atom, expr* rhs);
        void assert_axiom(expr* atom, expr* rhs);
        void add_date_term_axioms(expr* e);
        void add_op_axioms(app* term);
        bool link_normal_form(expr* e);

        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;

    public:
        solver(euf::solver& ctx, euf::theory_id id);

        euf::th_solver* clone(euf::solver& ctx) override;

        sat::literal internalize(expr* e, bool sign, bool root) override;

        void internalize(expr* e) override;

        euf::theory_var mk_var(euf::enode* n) override;

        void apply_sort_cnstr(euf::enode* n, sort* s) override;

        bool unit_propagate() override;

        bool use_diseqs() const override { return true; }

        void new_diseq_eh(euf::th_eq const& eq) override;

        bool is_external(sat::bool_var v) override { return false; }

        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override { UNREACHABLE(); }

        sat::check_result check() override {
            return m_qhead < m_rhs.size() ? sat::check_result::CR_CONTINUE : sat::check_result::CR_DONE;
        }

        std::ostream& display(std::ostream& out) const override;

        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return out; }

        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return out; }

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;

        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;

        // date.mk0 (the unspecified-constructor fallback) is treated as an
        // uninterpreted function; models record its interpretation so that
        // terms mentioning it evaluate consistently
        bool include_func_interp(func_decl* f) const override {
            return is_decl_of(f, get_id(), OP_DATE_MK0);
        }
    };
}
