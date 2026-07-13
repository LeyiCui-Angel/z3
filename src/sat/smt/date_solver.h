/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for calendar dates (SAT/EUF core).

    Mirrors smt::theory_date: every date operation is reduced to
    integer arithmetic over the internal injection
    date.epoch! : Date -> Int, and injectivity of the epoch map
    (epoch(a) = epoch(b) => a = b) is enforced lazily: eagerly for
    disequalities, and in response to merges of epoch terms. Epoch
    terms are shared between this solver and arithmetic, so the
    arithmetic solver's model-based theory combination (assume_eqs)
    proposes equalities between equal-valued epochs, which arrive
    here through new_eq_eh.

Author:

    Z3 date theory extension 2026-07-05

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "sat/smt/sat_th.h"

namespace euf {
    class solver;
}

namespace dates {

    class solver : public euf::th_euf_solver {
        // deferred axiom queue. Axioms create and internalize new
        // arithmetic terms; doing that from within internalization
        // re-enters the goal2sat conversion, which is not re-entrant
        // (its result stack is per-assertion). All axioms are queued
        // during internalization and flushed from unit_propagate().
        enum axiom_kind {
            AX_EQ,          // e1 = e2 (definitional axiom)
            AX_UNIT,        // e1 is a Bool constraint asserted as a unit axiom
            AX_CMP,         // e1 is a comparison atom to axiomatize
            AX_EPOCH_BOUND, // e1 is a Date term whose epoch is registered with arith
            AX_INJ,         // e1, e2 are Date terms: epoch(e1) = epoch(e2) => e1 = e2
            AX_COMPONENTS,  // e1 is a Date term: selector bounds and
                            // epoch = days-from-civil(selectors)
            AX_MK,          // e1 is a date.mk term: validity constraints + definition
            AX_MKINJ        // e1 is a Date term whose class contains date.mk terms:
                            // equal dates have equal components
        };

        date_util  u;
        arith_util a;

        svector<axiom_kind> m_kinds;
        expr_ref_vector     m_e1s, m_e2s;
        unsigned            m_qhead = 0;

        euf::theory_var mk_var(euf::enode* n) override;
        void track_date(euf::enode* n);
        void push_axiom(axiom_kind k, expr* e1, expr* e2 = nullptr);
        void assert_axiom_eq(expr* lhs, expr* rhs);
        void assert_unit_axiom(expr* e);
        void assert_cmp_axiom(app* atom);
        void assert_epoch_bound(expr* d);
        void assert_injectivity(expr* d1, expr* d2);
        void assert_mk_injectivity(euf::enode* n);
        void assert_component_axioms(expr* d);
        void assert_mk_axioms(app* mk);
        void internalize_date_op(app* term);
        bool epoch_value(euf::enode* n, rational& val);

        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;

    public:
        solver(euf::solver& ctx, euf::theory_id id);

        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override { UNREACHABLE(); }
        void asserted(sat::literal l) override {}
        sat::check_result check() override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return out; }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return out; }
        void collect_statistics(statistics& st) const override {}
        euf::th_solver* clone(euf::solver& ctx) override;
        bool unit_propagate() override;
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override;
        bool is_shared(euf::theory_var v) const override { return true; }
        void new_eq_eh(euf::th_eq const& eq) override;
        bool use_diseqs() const override { return true; }
        void new_diseq_eh(euf::th_eq const& eq) override;
        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override { dep.insert(n, nullptr); return true; }
    };

}
