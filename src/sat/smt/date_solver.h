/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for calendar dates in the SAT/EUF pipeline.

    Mirrors smt::theory_date: date constraints are reduced to linear
    integer arithmetic by eagerly instantiating the axioms of
    date_axioms for every internalized date term.

Author:

    Date theory extension 2026-07-05

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "ast/date_decl_plugin.h"
#include "ast/rewriter/date_axioms.h"
#include "ast/rewriter/th_rewriter.h"

namespace euf {
    class solver;
}

namespace date {

    class solver : public euf::th_euf_solver {
        typedef euf::theory_var theory_var;
        typedef euf::enode enode;

        date_util           u;
        arith_util          a;
        th_rewriter         m_rw;
        date_axioms         m_ax;
        obj_hashtable<expr> m_axiomatized;

        void add_axiom_clause(expr_ref_vector const& lits);
        void ensure_axioms(expr* e);
        expr* value_source(euf::enode* n, enode*& yn, enode*& mon, enode*& dn);

    public:
        solver(euf::solver& ctx, euf::theory_id id);

        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override {}
        void asserted(sat::literal l) override {}
        sat::check_result check() override { return sat::check_result::CR_DONE; }

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return out; }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return out; }
        void collect_statistics(statistics& st) const override {}
        euf::th_solver* clone(euf::solver& ctx) override;
        bool unit_propagate() override { return false; }

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;

        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;

        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override;
    };
}
