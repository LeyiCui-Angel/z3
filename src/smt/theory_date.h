/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory solver for calendar dates (legacy SMT core).

    The solver reduces all date operations to integer arithmetic over
    the internal injection date.epoch! : Date -> Int:

    - (date.mk y m d)        epoch(t) = epoch-of-ymd(y, m, d)
    - (date.add d py pm pd)  epoch(t) = epoch-of-add(epoch(d), py, pm, pd)
    - (date.sub d py pm pd)  epoch(t) = epoch-of-add(epoch(d), -py, -pm, -pd)
    - date.year/month/day    t = component-of-epoch(epoch(d))
    - date.lt/le/gt/ge       atom <=> epoch order

    All right-hand sides are linear integer arithmetic with ite and
    div/mod by constants. In addition, for every Date term d the
    tautology (or (<= epoch(d) 0) (>= epoch(d) 0)) is asserted so that
    epoch(d) is registered with the arithmetic solver and always has a
    value in the arithmetic model.

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
            AX_CMP,         // e1 is a comparison atom to axiomatize
            AX_EPOCH_BOUND, // e1 is a Date term whose epoch is registered with arith
            AX_INJ,         // e1, e2 are Date terms: epoch(e1) = epoch(e2) => e1 = e2
            AX_CIVIL,       // e1 is a Date term: epoch = days-from-civil(components)
            AX_MK           // e1 is a date.mk term: definition + in-range shortcut
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

        void push_axiom(axiom_kind k, expr* e1, expr* e2 = nullptr);
        bool flush_axioms();
        void assert_eq_axiom(expr* lhs, expr* rhs);
        void assert_cmp_axiom(app* atom);
        void assert_epoch_bound(expr* d);
        void assert_injectivity(expr* d1, expr* d2);
        void assert_civil_identity(expr* d);
        void assert_mk_axioms(app* mk);

        void ensure_var(enode* n);
        bool epoch_value(enode* n, rational& val);
        bool final_check();

    public:
        theory_date(context& ctx);

        char const* get_name() const override { return "date"; }
        theory* mk_fresh(context* new_ctx) override { return alloc(theory_date, *new_ctx); }
        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        bool can_propagate() override { return m_qhead < m_kinds.size(); }
        void propagate() override { flush_axioms(); }
        final_check_status final_check_eh(unsigned) override;
        void display(std::ostream& out) const override;
        void init_model(model_generator& mg) override;
        model_value_proc* mk_value(enode* n, model_generator& mg) override;
    };

}
