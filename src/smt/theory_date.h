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

    - the civil components (date.year d, date.month d, date.day d) of
      every date term d are constrained to range over valid in-range
      dates (year in [1..9999]) and to determine (date.epoch d)
    - (date.mk y m dd): the components are exactly (y, m, dd); combined
      with the validity bounds this makes occurrences with invalid
      argument triples (e.g. February 30th) infeasible
    - (date.epoch (date.add d ...))    = month-arithmetic with day
      clamping over the components of d, similarly for date.sub; the
      intermediate date of the month shift must be in range, and the
      result is a date term, hence in range as well
    - date.lt/le/gt/ge                <=> corresponding epoch comparison

    All formulas use only integer division by positive constants, which
    the arithmetic solver handles completely. The epoch map is a
    bijection between dates and the integer interval
    [min_epoch(), max_epoch()]; injectivity is enforced lazily: when
    the epochs of two date terms become equal the dates are equated,
    and when two date terms are asserted distinct their epochs are
    forced apart.

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

        // Defining axioms of a date term, built once per expression and
        // never popped: axioms of re-internalized terms then reuse the
        // same fresh constants and atoms as the original ones.
        // The axioms come in two layers. The epoch layer defines the epoch
        // day number of the term and keeps it inside
        // [min_epoch(), max_epoch()], which is all that comparisons,
        // equalities and models need. The civil layer introduces the
        // (year, month, day) components together with the epoch computation
        // over them; it is materialized lazily, only for terms whose
        // components are actually referenced (selector arguments, symbolic
        // date.mk applications, and the first argument of
        // date.add/date.sub).
        struct rep_axioms {
            expr_ref        m_epoch_def;   // epoch value of the term
            expr_ref        m_epoch_def2;  // second epoch equation of date.add/date.sub terms
            expr_ref_vector m_epoch_fmls;
            expr_ref        m_year, m_month, m_day;
            expr_ref        m_civil_def;   // epoch computed from the components
            expr_ref_vector m_civil_fmls;
            rep_axioms(ast_manager& m):
                m_epoch_def(m), m_epoch_def2(m), m_epoch_fmls(m),
                m_year(m), m_month(m), m_day(m), m_civil_def(m), m_civil_fmls(m) {}
        };

        date_util         u;
        th_rewriter       m_rw;
        svector<var_rep>  m_var2rep;
        obj_map<expr, rep_axioms*> m_reps;
        expr_ref_vector   m_trail;
        date_factory*     m_factory { nullptr };

        theory_var mk_var(enode* n) override;
        void ensure_epoch(enode* n);
        void ensure_civil(enode* n);
        void set_civil(theory_var v, rep_axioms const& ra);
        rep_axioms& get_rep_axioms(app* t);
        void build_civil(app* t, rep_axioms& ra);
        void link_eq(expr* x, expr* y);
        void assert_axiom(expr* e);
        void assert_axioms(expr_ref_vector const& fmls);
        void assert_axiom_eq(expr* lhs, expr* rhs);
        void internalize_cmp(app* atom);

        class date_value_proc;

    public:
        theory_date(context& ctx);
        ~theory_date() override;

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
