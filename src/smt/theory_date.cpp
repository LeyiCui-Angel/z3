/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Legacy-SMT theory solver for the native theory of calendar dates.
    See theory_date.h, ast/date_axioms.h and Dates.smt2.

Author:

    Angel Cui 2026

--*/

#include "smt/theory_date.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "ast/ast_pp.h"

namespace smt {

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        du(ctx.get_manager()),
        a(ctx.get_manager()),
        m_gen(ctx.get_manager()),
        m_rw(ctx.get_manager()),
        m_axioms(ctx.get_manager()) {
    }

    theory_var theory_date::mk_var(enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        theory_var v = theory::mk_var(n);
        ctx.attach_th_var(n, this, v);
        ctx.mark_as_relevant(n);
        return v;
    }

    void theory_date::emit_date_axioms(expr* t) {
        if (!du.is_date(t) || m_processed.contains(t))
            return;
        m_processed.insert(t);
        m_gen.reduce_term(t, m_axioms);
    }

    void theory_date::internalize_predicate(app* atom) {
        if (m_processed.contains(atom))
            return;
        m_processed.insert(atom);
        m_gen.reduce_atom(atom, m_axioms);
    }

    // Rewrite and assert every buffered axiom.  Called only once the term is
    // fully built, so no raw intermediate terms are live during rewriting.
    void theory_date::flush_axioms() {
        while (!m_axioms.empty()) {
            expr_ref_vector batch(m);
            batch.swap(m_axioms);
            for (expr* e0 : batch) {
                expr_ref e(e0, m);
                m_rw(e);
                if (m.is_true(e))
                    continue;
                literal l = mk_literal(e);
                ctx.mark_as_relevant(l);
                ctx.mk_th_axiom(get_id(), 1, &l);
            }
        }
    }

    bool theory_date::internalize_atom(app* atom, bool gate_ctx) {
        SASSERT(atom->get_family_id() == get_id());
        for (expr* arg : *atom)
            mk_var(ensure_enode(arg));
        if (!ctx.b_internalized(atom)) {
            bool_var bv = ctx.mk_bool_var(atom);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }
        for (expr* arg : *atom)
            emit_date_axioms(arg);
        internalize_predicate(atom);
        flush_axioms();
        return true;
    }

    bool theory_date::internalize_term(app* term) {
        SASSERT(term->get_family_id() == get_id());
        for (expr* arg : *term)
            mk_var(ensure_enode(arg));

        enode* e = ctx.e_internalized(term) ? ctx.get_enode(term)
                                            : ctx.mk_enode(term, false, false, true);
        mk_var(e);

        for (expr* arg : *term)
            emit_date_axioms(arg);
        emit_date_axioms(term);
        flush_axioms();
        return true;
    }

    void theory_date::apply_sort_cnstr(enode* n, sort* s) {
        if (!du.is_date_sort(s))
            return;
        mk_var(n);
        emit_date_axioms(n->get_expr());
        flush_axioms();
    }

    // ----- model generation ------------------------------------------------

    namespace {
        class date_value_proc : public model_value_proc {
            date_util& du;
            enode* m_y;
            enode* m_m;
            enode* m_d;
        public:
            date_value_proc(date_util& du, enode* y, enode* mo, enode* d):
                du(du), m_y(y), m_m(mo), m_d(d) {}
            void get_dependencies(buffer<model_value_dependency>& result) override {
                result.push_back(model_value_dependency(m_y));
                result.push_back(model_value_dependency(m_m));
                result.push_back(model_value_dependency(m_d));
            }
            app* mk_value(model_generator& mg, expr_ref_vector const& values) override {
                return du.mk_mk(values[0], values[1], values[2]);
            }
        };
    }

    void theory_date::init_model(model_generator& mg) {}

    model_value_proc* theory_date::mk_value(enode* n, model_generator& mg) {
        expr_ref ye(du.mk_year(n->get_expr()), m);
        expr_ref me(du.mk_month(n->get_expr()), m);
        expr_ref de(du.mk_day(n->get_expr()), m);
        if (ctx.e_internalized(ye) && ctx.e_internalized(me) && ctx.e_internalized(de))
            return alloc(date_value_proc, du,
                         ctx.get_enode(ye), ctx.get_enode(me), ctx.get_enode(de));
        return alloc(expr_wrapper_proc, to_app(du.plugin().get_some_value(n->get_sort())));
    }

}
