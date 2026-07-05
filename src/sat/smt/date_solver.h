/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.h

Abstract:

    Theory solver for calendar dates (SAT/EUF core).

    Mirrors smt::theory_date: every date operation is reduced to
    integer arithmetic over the internal injection
    date.epoch! : Date -> Int, and injectivity of the epoch map
    (epoch(a) = epoch(b) => a = b) is enforced lazily for
    disequalities and at final check.

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
        date_util  u;
        arith_util a;

        euf::theory_var mk_var(euf::enode* n) override;
        void track_date(euf::enode* n);
        void assert_axiom_eq(expr* lhs, expr* rhs);
        void assert_injectivity(euf::enode* n1, euf::enode* n2);
        void assert_civil_identity(expr* d);
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
        bool unit_propagate() override { return false; }
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        void apply_sort_cnstr(euf::enode* n, sort* s) override;
        bool use_diseqs() const override { return true; }
        void new_diseq_eh(euf::th_eq const& eq) override;
        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override { dep.insert(n, nullptr); return true; }
    };

}
