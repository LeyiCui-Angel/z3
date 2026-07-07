/*++
Copyright (c) 2026 Theoria

Module Name:

    elim_dates_tactic.cpp

Abstract:

    Tactic that eliminates the theory of calendar dates from a goal by
    reduction to integer arithmetic.

Author:

    Claude (Theoria date theory) 2026-07-07

--*/
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/date_rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/converters/generic_model_converter.h"
#include "tactic/tactical.h"

namespace {

struct elim_dates_rw_cfg : public default_rewriter_cfg {
    ast_manager &                m;
    date_rewriter                m_rw;
    arith_util                   m_arith;
    obj_map<func_decl, expr*>    m_const2days;
    expr_ref_vector              m_pinned;
    generic_model_converter *    m_mc = nullptr;

    elim_dates_rw_cfg(ast_manager & m):
        m(m),
        m_rw(m),
        m_arith(m),
        m_pinned(m) {}

    date_util & u() { return m_rw.u(); }

    bool max_steps_exceeded(unsigned num_steps) const { return false; }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = nullptr;
        family_id fid = f->get_family_id();
        if (fid == m_rw.get_fid())
            return m_rw.mk_app_core(f, num, args, result);
        if (m.is_eq(f) && num == 2 && u().is_date(args[0]))
            return m_rw.mk_eq_core(args[0], args[1], result);
        if (m.is_distinct(f) && num > 0 && u().is_date(args[0]))
            return m_rw.mk_distinct_core(num, args, result);
        if (fid == null_family_id && num == 0 && u().is_date_sort(f->get_range())) {
            expr * days = nullptr;
            if (!m_const2days.find(f, days)) {
                app * k = m.mk_fresh_const(f->get_name(), m_arith.mk_int());
                days = k;
                m_pinned.push_back(k);
                m_const2days.insert(f, days);
                if (m_mc) {
                    m_mc->hide(k->get_decl());
                    m_mc->add(f, u().mk_from_days(k));
                }
            }
            result = u().mk_from_days(days);
            return BR_DONE;
        }
        return BR_FAILED;
    }
};

struct elim_dates_rw : public rewriter_tpl<elim_dates_rw_cfg> {
    elim_dates_rw_cfg m_cfg;
    elim_dates_rw(ast_manager & m):
        rewriter_tpl<elim_dates_rw_cfg>(m, false, m_cfg),
        m_cfg(m) {}
};

class elim_dates_tactic : public tactic {
    ast_manager & m;
    params_ref    m_params;

    struct has_date_pred {
        date_util & u;
        has_date_pred(date_util & u):u(u) {}
        void operator()(var * n) { test(n->get_sort()); }
        void operator()(app * n) {
            if (n->get_family_id() == u.get_family_id())
                throw found();
            test(n->get_sort());
        }
        void operator()(quantifier * n) {}
        void test(sort * s) {
            if (u.sort_contains_date(s))
                throw found();
        }
        struct found {};
    };

    bool has_dates(goal const & g, date_util & u) {
        has_date_pred p(u);
        try {
            for (unsigned i = 0; i < g.size(); ++i)
                quick_for_each_expr(p, g.form(i));
        }
        catch (has_date_pred::found const &) {
            return true;
        }
        return false;
    }

public:
    elim_dates_tactic(ast_manager & m, params_ref const & p):
        m(m),
        m_params(p) {}

    tactic * translate(ast_manager & other_m) override {
        return alloc(elim_dates_tactic, other_m, m_params);
    }

    char const* name() const override { return "elim_dates"; }

    void updt_params(params_ref const & p) override { m_params.append(p); }

    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        tactic_report report("elim-dates", *g);
        date_util u(m);
        // fast path: nothing date-related in the goal, and proofs are not
        // supported (the th_rewriter based reduction still applies there).
        if (g->proofs_enabled() || !has_dates(*g, u)) {
            result.push_back(g.get());
            return;
        }
        elim_dates_rw rw(m);
        generic_model_converter_ref mc;
        if (g->models_enabled()) {
            mc = alloc(generic_model_converter, m, "elim_dates");
            rw.m_cfg.m_mc = mc.get();
        }
        expr_ref new_curr(m);
        for (unsigned idx = 0; idx < g->size(); ++idx) {
            rw(g->form(idx), new_curr);
            g->update(idx, new_curr, nullptr, g->dep(idx));
        }
        if (mc)
            g->add(mc.get());
        g->inc_depth();
        result.push_back(g.get());
    }

    void cleanup() override {}
};

}

tactic * mk_elim_dates_tactic(ast_manager & m, params_ref const & p) {
    return alloc(elim_dates_tactic, m, p);
}
