/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory solver for calendar dates (legacy SMT core).

    The solver reduces all date operations to integer arithmetic over
    the internal injection date.epoch! : Date -> Int. The encoding is
    purely *forward* (relational): where the components of a date are
    needed, its selector terms (date.year d) etc. serve as the component
    variables, constrained by the component axioms

        1 <= month(d) <= 12,  1 <= day(d) <= days-in-month(year(d), month(d)),
        epoch(d) = days-from-civil(year(d), month(d), day(d))

    (asserted on demand, per Date term). The operations become

    - (date.mk y m d)        1 <= m <= 12, 1 <= d <= days-in-month(y, m),
                             epoch(t) = days-from-civil(y, m, d),
                             year(t) = y, month(t) = m, day(t) = d
    - (date.add d py pm pd)  epoch(t) = epoch-of-add over epoch(d) and
                             the components of d (plus component axioms
                             for d); pure day shifts reduce to
                             epoch(t) = epoch(d) + pd
    - (date.sub d py pm pd)  date.add with negated offsets
    - date.year/month/day    component axioms for d; the selector term
                             itself is the component
    - date.lt/le/gt/ge       atom <=> epoch order

    All right-hand sides are linear integer arithmetic with ite and
    div/mod by small constants (4, 100, 400, 12). The inverse
    civil-of-epoch map is never encoded symbolically: recovering
    components from an epoch is left to the integer solver's search over
    the bounded component variables. In addition, for every Date term d
    the tautology (or (<= epoch(d) 0) (>= epoch(d) 0)) is asserted so
    that epoch(d) is registered with the arithmetic solver and always
    has a value in the arithmetic model.

    The axioms are queued during internalization and flushed in
    propagate(), because internalization of date terms can be nested
    inside the internalization of arithmetic atoms.

    The only genuinely theory-specific reasoning is injectivity of the
    epoch map: epoch(a) = epoch(b) => a = b, asserted lazily for
    disequalities and at final check for distinct date classes whose
    epochs coincide in the arithmetic model.

Author:

    Z3 date theory extension 2026-07-05

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/date_factory.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"

namespace smt {

    class theory_date : public theory {
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

        date_util       u;
        arith_util      a;
        th_rewriter     m_rw;
        arith_value     m_avalue;
        date_factory*   m_factory { nullptr };

        // deferred axiom queue
        svector<axiom_kind> m_kinds;
        expr_ref_vector     m_e1s, m_e2s;
        unsigned            m_qhead { 0 };

        // month-window starts (resp. hint values) already emitted, per
        // date term; dampers for propagate_windows (not backtracked,
        // safe because the lemmas are valid and redundant)
        obj_map<expr, vector<rational>> m_emitted;
        obj_map<expr, vector<rational>> m_chain_emitted;
        obj_map<expr, vector<rational>> m_cover_emitted;
        // rounds a constant-shift term has been inexact with nothing new
        // to emit; at a threshold the term is escalated to the eager tier
        obj_map<expr, unsigned> m_stuck;
        // cumulative count of chain-window lemmas emitted per term (the
        // march detector: a healthy repair uses a handful of windows)
        obj_map<expr, unsigned> m_clears;
        // date terms whose selectors occur in the input formula (as
        // opposed to selector terms created by this solver's own lemmas)
        obj_hashtable<expr>     m_sel_terms;
        // epoch model values seen at the previous propagate_windows call;
        // lemmas are only emitted when the snapshot is unchanged, i.e.
        // when the arithmetic assignment has settled -- values read while
        // the integer search is still moving are garbage and chasing
        // them pollutes the emission history
        obj_map<expr, rational> m_last_vals;
        // extreme epoch positions observed per inexact chain term (the
        // march detector's drift range)
        obj_map<expr, rational> m_pos_lo;
        obj_map<expr, rational> m_pos_hi;
        obj_hashtable<expr>     m_escalated;

        // comparison atoms and date disequalities seen so far, for the
        // placement search (trail-backtracked alongside the axiom queue)
        expr_ref_vector m_cmp_atoms;
        expr_ref_vector m_dq1s, m_dq2s;

        void push_axiom(axiom_kind k, expr* e1, expr* e2 = nullptr);
        bool flush_axioms();
        void assert_eq_axiom(expr* lhs, expr* rhs);
        void assert_unit_axiom(expr* e);
        void assert_cmp_axiom(app* atom);
        void assert_epoch_bound(expr* d);
        void assert_injectivity(expr* d1, expr* d2);
        void assert_component_axioms(expr* d);
        void assert_mk_axioms(app* mk);
        void push_shift_axioms(app* term, expr* b, expr* py, expr* pm);
        void escalate_shift(expr* t);
        void assert_mk_injectivity(expr* e);

        void ensure_var(enode* n);
        bool epoch_value(enode* n, rational& val);
        bool final_check();
        bool implied_epoch(expr* t, obj_map<expr, rational>& memo, rational& z);
        bool propagate_windows();

    public:
        theory_date(context& ctx);

        char const* get_name() const override { return "date"; }
        theory* mk_fresh(context* new_ctx) override { return alloc(theory_date, *new_ctx); }
        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        bool can_propagate() override { return m_qhead < m_kinds.size(); }
        void propagate() override { flush_axioms(); }
        final_check_status final_check_eh(unsigned) override;
        void display(std::ostream& out) const override;
        void init_model(model_generator& mg) override;
        model_value_proc* mk_value(enode* n, model_generator& mg) override;
    };

}
