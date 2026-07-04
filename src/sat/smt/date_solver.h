/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    SAT/EUF theory solver for the native theory of calendar dates.

    Like theory_date in the legacy pipeline, this is a lazy reduction
    theory: every Date term and date comparison atom is reduced (via the
    shared date_axiom_gen) to defining axioms over the integer projections
    date.year / date.month / date.day, which are asserted into the EUF/SAT
    core.  All real reasoning is delegated to the arithmetic + EUF solvers.

    See ast/date_axioms.h and Dates.smt2 for the specification.

Author:

    Angel Cui 2026

--*/
#pragma once

#include "sat/smt/euf_solver.h"
#include "ast/date_axioms.h"
#include "ast/rewriter/th_rewriter.h"

namespace date {

    typedef euf::enode enode;
    typedef euf::theory_var theory_var;

    class solver : public euf::th_euf_solver {
        typedef euf::theory_id theory_id;
        typedef sat::bool_var bool_var;
        typedef sat::literal literal;
        typedef sat::literal_vector literal_vector;

        date_util           du;
        date_axiom_gen      m_gen;
        th_rewriter         m_th_rw;         // normalize the reduced arithmetic
        obj_hashtable<expr> m_processed;     // terms/atoms already reduced
        expr_ref_vector     m_axioms;        // pending reduced axioms
        svector<std::tuple<enode*, bool, bool>> m_nodes;
        unsigned            m_nodes_qhead = 0;

        void flush_axioms();
        void reduce(enode* n);

        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        euf::theory_var mk_var(enode* n) override;

    public:
        solver(euf::solver& ctx, theory_id id);

        bool is_external(bool_var v) override { return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) override {}
        void asserted(literal l) override {}
        sat::check_result check() override { return sat::check_result::CR_DONE; }
        bool unit_propagate() override;

        std::ostream& display(std::ostream& out) const override { return out; }
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return euf::th_explain::from_index(idx).display(out); }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return display_justification(out, idx); }

        void collect_statistics(statistics& st) const override {}
        euf::th_solver* clone(euf::solver& ctx) override { return alloc(solver, ctx, get_id()); }

        void new_eq_eh(euf::th_eq const& eq) override {}
        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;

        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
    };
}
