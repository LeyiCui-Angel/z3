/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for calendar dates for the SAT/EUF core.

    The solver mirrors smt::theory_date: date constraints are reduced
    to linear integer arithmetic over the selector triples
    (date.year t, date.month t, date.day t) of the Date terms.
    Axioms are produced lazily from a queue of internalized terms.

Author:

    Angel Cui 2026-03-23

--*/
#pragma once

#include "util/obj_pair_hashtable.h"
#include "sat/smt/sat_th.h"
#include "ast/date_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"

namespace euf {
    class solver;
}

namespace date {

    class solver : public euf::th_euf_solver {
        typedef euf::theory_var theory_var;
        typedef euf::enode enode;
        typedef sat::literal literal;

        date_util     u;
        arith_util    a;
        th_rewriter   m_rw;
        ptr_vector<euf::enode> m_nodes;
        unsigned      m_nodes_qhead = 0;
        obj_pair_hashtable<expr, expr> m_diseq_seen;
        expr_ref_vector m_diseq_trail;
        indexed_uint_set m_year_pref_vars;

        void attach_new_th_var(enode* n);
        bool selector_enodes(euf::enode* n, euf::enode*& y, euf::enode*& mo, euf::enode*& d);
        void add_axioms(enode* n);
        void add_date_axioms(expr* t);
        void add_mk_axioms(app* t);
        void add_arith_axioms(app* t, bool is_sub);
        void add_cmp_axioms(app* atom);
        void assert_unit(expr* e);
        void add_year_range_preference(expr* y);
        void assert_unit_norewrite(expr* e);
        void assert_implies(expr* premise, expr* conseq);
        void assert_iff(literal lit, expr* def);
        expr_ref mk_lex_cmp(expr* x, expr* y, bool strict);
        expr_ref mk_rata_die(expr* d);
        expr* mk_neg(expr* e);

    public:
        solver(euf::solver& ctx, euf::theory_id id);

        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override {}
        void asserted(literal l) override {}
        sat::check_result check() override;
        bool unit_propagate() override;
        bool decide(sat::bool_var& var, lbool& phase) override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return out; }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return out; }
        void collect_statistics(statistics& st) const override {}
        euf::th_solver* clone(euf::solver& ctx) override;
        bool use_diseqs() const override { return true; }
        void new_diseq_eh(euf::th_eq const& eq) override;

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;

        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override;
    };
}
