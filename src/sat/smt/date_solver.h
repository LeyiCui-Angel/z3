/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for calendar dates (SAT/EUF core).

    Mirrors smt::theory_date: date operations are reduced to linear
    integer arithmetic over the selector terms of every Date term, and
    extensionality is enforced lazily at final check guided by the
    arithmetic model.

Author:

    Claude (Anthropic) 2026-07-04

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
        typedef euf::theory_var theory_var;
        typedef euf::theory_id theory_id;
        typedef euf::enode enode;
        typedef sat::literal literal;
        typedef sat::literal_vector literal_vector;

        date_util           m_util;
        arith_util          m_arith;
        th_rewriter         m_rewrite;
        obj_hashtable<expr> m_axiomatized;
        ptr_vector<expr>    m_terms;      // axiomatized terms of sort Date

        date_util& u() { return m_util; }
        bool is_date(expr* e) const { return m_util.is_date(e->get_sort()); }

        void assert_axiom(expr* fml);
        void ensure_axioms(expr* t);
        void internalize_cmp(app* atom);
        expr* find_axiomatized(enode* n);

    public:
        solver(euf::solver& ctx, theory_id id);

        euf::th_solver* clone(euf::solver& ctx) override;

        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) override {}
        void asserted(literal l) override {}
        sat::check_result check() override;
        bool unit_propagate() override { return false; }

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return euf::th_explain::from_index(idx).display(out); }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return display_justification(out, idx); }
        void collect_statistics(statistics& st) const override {}

        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        void apply_sort_cnstr(enode* n, sort* s) override;

        void add_value(enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(enode* n, top_sort<enode>& dep) override;
        bool include_func_interp(func_decl* f) const override { return false; }

        euf::theory_var mk_var(enode* n) override;
    };
}
