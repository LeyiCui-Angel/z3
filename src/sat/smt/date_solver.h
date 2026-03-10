/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for calendar dates and periods (new SAT/SMT core).

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"

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

        date_decl_plugin& m_plugin;
        arith_util        m_autil;

        // Internal skolem func_decls for date components
        func_decl_ref m_date_year;
        func_decl_ref m_date_month;
        func_decl_ref m_date_day;

        obj_hashtable<expr> m_axiomatized;

        void ensure_date_selectors();
        app_ref mk_date_year(expr* d);
        app_ref mk_date_month(expr* d);
        app_ref mk_date_day(expr* d);
        app_ref mk_period_years(expr* p);
        app_ref mk_period_months(expr* p);
        app_ref mk_period_days(expr* p);
        app_ref mk_mk_date(expr* y, expr* mo, expr* d);
        app_ref mk_mk_period(expr* y, expr* mo, expr* d);

        void assert_eq_axiom(expr* lhs, expr* rhs);
        void assert_iff_axiom(expr* lhs, expr* rhs);

        void axiomatize_mk_date(expr* term);
        void axiomatize_mk_period(expr* term);
        void axiomatize_date_add(expr* term);
        void axiomatize_date_sub(expr* term);
        void axiomatize_period_add(expr* term);
        void axiomatize_period_sub(expr* term);
        void axiomatize_period_mul(expr* term);
        void axiomatize_date_cmp(expr* term, decl_kind k);
        void axiomatize_date_reconstruction(expr* e);
        void axiomatize_period_reconstruction(expr* e);

        bool has_axiom(expr* e) { return m_axiomatized.contains(e); }
        void mark_axiomatized(expr* e) { m_axiomatized.insert(e); }

        void pop_core(unsigned n) override;

        // Internalization
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;

    public:
        solver(euf::solver& ctx, theory_id id);
        ~solver() override {}

        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) override;
        void asserted(literal l) override {}
        sat::check_result check() override;
        bool unit_propagate() override { return false; }

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return euf::th_explain::from_index(idx).display(out); }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return display_justification(out, idx); }
        void collect_statistics(statistics& st) const override {}
        euf::th_solver* clone(euf::solver& ctx) override;
        void new_eq_eh(euf::th_eq const& eq) override {}

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;
        bool include_func_interp(func_decl* f) const override;
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        euf::theory_var mk_var(euf::enode* n) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override;
        bool is_shared(theory_var v) const override { return false; }
        lbool get_phase(sat::bool_var v) override { return l_true; }
    };
}
