/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for calendar dates (SAT/EUF pipeline).

    Works by reduction to integer arithmetic, mirroring
    smt::theory_date: every Date term is characterized by the integer
    triple of its selectors, and the theory semantics are asserted as
    lemmas over those triples (validity, reconstruction, constructor
    inversion, Rata Die day-number shifts for date.add/date.sub,
    lexicographic comparisons, and order/equality bridges between pairs
    of Date terms).

Author:

    Claude 2026-07-05

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "ast/date_decl_plugin.h"
#include "ast/rewriter/date_rewriter.h"

namespace euf {
    class solver;
}

namespace date {

    class solver : public euf::th_euf_solver {
        typedef euf::theory_var theory_var;
        typedef euf::theory_id theory_id;
        typedef euf::enode enode;
        typedef sat::literal literal;

        date_util       dt;
        arith_util      a;
        date_axioms     ax;

        // Pending axiom instantiations, drained by unit_propagate.
        // Clauses in the SAT/EUF core persist across backtracking, so
        // each axiom is asserted exactly once.
        expr_ref_vector m_axioms;
        unsigned        m_axioms_qhead = 0;

        expr_ref_vector m_dates;
        obj_hashtable<expr> m_seen;

        void push_axiom(expr* e);
        void add_date_term(app* t);
        euf::theory_var mk_var(enode* n) override;
        bool find_triple(enode* n, enode*& y, enode*& mo, enode*& d);

    public:
        solver(euf::solver& ctx, theory_id id);

        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override {}
        void asserted(literal l) override {}
        sat::check_result check() override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return out; }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return out; }
        void collect_statistics(statistics& st) const override {}
        euf::th_solver* clone(euf::solver& ctx) override;
        void new_eq_eh(euf::th_eq const& eq) override {}
        bool unit_propagate() override;
        void add_value(enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(enode* n, top_sort<enode>& dep) override;
        bool include_func_interp(func_decl* f) const override { return false; }
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
    };
}
