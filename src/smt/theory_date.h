/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    theory_date.h

Abstract:

    Theory solver for calendar dates and periods.

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_date : public theory {

        date_decl_plugin& m_plugin;
        arith_util        m_autil;

        // Internal skolem func_decls for extracting date components
        func_decl_ref     m_date_year;
        func_decl_ref     m_date_month;
        func_decl_ref     m_date_day;

        // Track which terms have had axioms asserted
        expr_ref_vector   m_axiom_trail;
        obj_hashtable<expr> m_axiomatized;

        // Helpers
        void ensure_date_selectors();
        app_ref mk_date_year(expr* d);
        app_ref mk_date_month(expr* d);
        app_ref mk_date_day(expr* d);

        app_ref mk_period_years(expr* p);
        app_ref mk_period_months(expr* p);
        app_ref mk_period_days(expr* p);

        app_ref mk_mk_date(expr* y, expr* mo, expr* d);
        app_ref mk_mk_period(expr* y, expr* mo, expr* d);

        void assert_axiom(literal l);
        void assert_axiom(literal l1, literal l2);
        void assert_eq_axiom(expr* lhs, expr* rhs);
        void assert_iff_axiom(expr* lhs, expr* rhs);

        void internalize_mk_date(app* term, enode* e);
        void internalize_mk_period(app* term, enode* e);
        void internalize_period_selector(app* term, enode* e);
        void internalize_date_add(app* term, enode* e);
        void internalize_date_sub(app* term, enode* e);
        void internalize_period_add(app* term, enode* e);
        void internalize_period_sub(app* term, enode* e);
        void internalize_period_mul(app* term, enode* e);
        void internalize_date_cmp(app* term, enode* e, decl_kind k, bool_var bv);

        void assert_date_accessor_axioms(enode* n);
        void assert_period_accessor_axioms(enode* n);
        void assert_date_reconstruction(enode* n);
        void assert_period_reconstruction(enode* n);

        bool has_axiom(expr* e);
        void mark_axiomatized(expr* e);

        theory_var mk_var(enode* n) override;

    public:
        theory_date(context& ctx);
        ~theory_date() override;

        theory* mk_fresh(context* new_ctx) override { return alloc(theory_date, *new_ctx); }

        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void apply_sort_cnstr(enode* n, sort* s) override;

        void new_eq_eh(theory_var v1, theory_var v2) override;
        bool use_diseqs() const override { return false; }
        void new_diseq_eh(theory_var v1, theory_var v2) override {}

        bool build_models() const override { return false; }
        final_check_status final_check_eh(unsigned) override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void reset_eh() override;

        void display(std::ostream& out) const override;
        char const* get_name() const override { return "date"; }
    };
}
