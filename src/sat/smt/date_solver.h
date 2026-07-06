/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for calendar dates in the SAT/EUF pipeline.

    Mirrors smt::theory_date: date constraints are reduced to linear
    integer arithmetic. Every Date term is constrained to have a
    calendar-valid selector triple and is identified with its
    reconstruction through date.mk; date.mk selector equations are
    guarded by validity of the argument triple; date.add/date.sub and
    the comparisons are characterized through the day-number (rata die)
    bijection between calendar-valid dates and the integers.

Author:

    Claude 2026-07-04

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "ast/date_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"

namespace euf {
    class solver;
}

namespace date {

    class solver : public euf::th_euf_solver {
        date_util   u;
        th_rewriter m_rw;
        // date.mk terms created internally by add_arith_axioms; their
        // argument validity is entailed by construction, so the implicit
        // validity obligation is not re-asserted for them
        obj_hashtable<expr> m_internal_mk;
        expr_ref_vector     m_internal_pinned;

        euf::theory_var mk_var(euf::enode* n) override;
        void add_axiom_unit(expr* e);
        void add_axiom_unit_raw(expr* e);
        void add_date_axioms(euf::enode* n);
        void add_mk_axioms(app* t);
        void add_arith_axioms(app* t);
        void add_cmp_axioms(sat::literal lit, app* atom);
        void add_injectivity_axioms(expr* x, euf::theory_var v);
        euf::enode* selector_enode(euf::enode* n, decl_kind k) const;

    public:
        solver(euf::solver& ctx, euf::theory_id id);

        void asserted(sat::literal l) override {}
        sat::check_result check() override { return sat::check_result::CR_DONE; }

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return out; }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return out; }
        void collect_statistics(statistics& st) const override {}
        euf::th_solver* clone(euf::solver& ctx) override;
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override {}
        bool unit_propagate() override { return false; }

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;
        bool include_func_interp(func_decl* f) const override { return false; }

        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override;
    };
}
