/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory solver for calendar dates (legacy SMT core).
    See date_decl_plugin.h for the semantics of the theory.

    The solver reduces date reasoning to linear integer arithmetic.
    Every term d of sort Date is associated with an integer term
    (date.epoch d), its epoch day number, and the date operations are
    axiomatized over epochs:

    - (date.epoch (date.mk y m dd))    = days-from-civil(y, m, dd)
    - (date.epoch (date.add d ...))    = month-arithmetic with day clamping
      over (date.epoch d), similarly for date.sub
    - (date.year d) / (date.month d) / (date.day d)
                                       = civil-from-days(date.epoch d)
    - date.lt/le/gt/ge                <=> corresponding epoch comparison

    All formulas use only integer division by positive constants, which
    the arithmetic solver handles completely. The epoch map is a
    bijection between dates and integers; injectivity is enforced
    lazily: when the epochs of two date terms become equal the dates
    are equated, and when two date terms are asserted distinct their
    epochs are forced apart.

Author:

    Angel Cui's date theory task 2026-07-04

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/date_factory.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_date : public theory {
        // epoch and civil component terms of a date-sorted theory variable
        struct var_rep {
            enode* m_epoch { nullptr };
            expr*  m_year { nullptr };
            expr*  m_month { nullptr };
            expr*  m_day { nullptr };
        };

        date_util         u;
        th_rewriter       m_rw;
        svector<var_rep>  m_var2rep;
        expr_ref_vector   m_trail;
        date_factory*     m_factory { nullptr };

        theory_var mk_var(enode* n) override;
        void ensure_rep(enode* n);
        void assert_axiom(expr* e);
        void assert_axioms(expr_ref_vector const& fmls);
        void assert_axiom_eq(expr* lhs, expr* rhs);
        void internalize_cmp(app* atom);

        class date_value_proc;

    public:
        theory_date(context& ctx);

        theory* mk_fresh(context* new_ctx) override { return alloc(theory_date, *new_ctx); }
        char const* get_name() const override { return "date"; }

        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        void pop_scope_eh(unsigned num_scopes) override;
        final_check_status final_check_eh(unsigned) override { return FC_DONE; }
        void display(std::ostream& out) const override {}

        void init_model(model_generator& mg) override;
        model_value_proc* mk_value(enode* n, model_generator& mg) override;
    };

}
