/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Theory solver for calendar dates in the legacy SMT pipeline.

Author:

    Date theory extension 2026-07-05

--*/
#include "smt/theory_date.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "ast/ast_pp.h"

namespace smt {

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        u(m),
        a(m),
        m_rw(m),
        m_ax(m, [this](expr_ref_vector const& lits) { add_clause(lits); }) {
    }

    void theory_date::add_clause(expr_ref_vector const& lits) {
        literal_vector ls;
        for (expr* e : lits) {
            // normalize the literal: the arithmetic solver expects
            // simplified atoms. Date comparison atoms are kept as is:
            // they define themselves through these clauses.
            expr* pos = e;
            m.is_not(e, pos);
            expr_ref r(e, m);
            if (!is_app_of(pos, get_family_id(), OP_DATE_LT) &&
                !is_app_of(pos, get_family_id(), OP_DATE_LE) &&
                !is_app_of(pos, get_family_id(), OP_DATE_GT) &&
                !is_app_of(pos, get_family_id(), OP_DATE_GE))
                m_rw(r);
            if (m.is_true(r))
                return;
            if (m.is_false(r))
                continue;
            literal lit = mk_literal(r);
            ctx.mark_as_relevant(lit);
            ls.push_back(lit);
        }
        ctx.mk_th_axiom(get_id(), ls);
    }

    void theory_date::ensure_axioms(expr* e) {
        SASSERT(u.is_date(e));
        if (m_axiomatized.contains(e))
            return;
        m_axiomatized.insert(e);
        ctx.push_trail(insert_obj_trail<expr>(m_axiomatized, e));
        // If the term simplifies (e.g. date.sub to date.add, or concrete
        // evaluation), link it to its simplified form and axiomatize that
        // form instead. The axioms below would otherwise be rewritten away
        // from this term when their literals are normalized.
        auto add_unit = [&](expr* f) {
            literal lit = mk_literal(f);
            ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), 1, &lit);
        };
        expr_ref r(e, m);
        m_rw(r);
        if (r.get() != e) {
            add_unit(m.mk_eq(e, r));
            return;
        }
        // For concrete valid constructor values pin the selectors directly:
        // the guarded selector axioms would be folded away by normalization
        // without ever creating the selector terms.
        rational vy, vm, vd;
        if (u.is_date_value(e, vy, vm, vd)) {
            add_unit(m.mk_eq(u.mk_year(e), a.mk_int(vy)));
            add_unit(m.mk_eq(u.mk_month(e), a.mk_int(vm)));
            add_unit(m.mk_eq(u.mk_day(e), a.mk_int(vd)));
            return;
        }
        m_ax.date_term_axioms(e);
        if (u.is_mk(e))
            m_ax.mk_axioms(to_app(e));
        else if (u.is_add(e) || u.is_sub(e))
            m_ax.add_axioms(to_app(e));
    }

    bool theory_date::internalize_atom(app * atom, bool gate_ctx) {
        SASSERT(u.is_lt(atom) || u.is_le(atom) || u.is_gt(atom) || u.is_ge(atom));
        for (expr* arg : *atom)
            ensure_enode(arg);
        if (!ctx.b_internalized(atom)) {
            bool_var bv = ctx.mk_bool_var(atom);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }
        m_ax.cmp_axioms(atom);
        return true;
    }

    bool theory_date::internalize_term(app * term) {
        for (expr* arg : *term)
            ensure_enode(arg);
        if (!ctx.e_internalized(term))
            ctx.mk_enode(term, false, m.is_bool(term), true);
        // for terms of sort Date the context invokes apply_sort_cnstr,
        // which instantiates the axioms; selector terms need no variable
        // of this theory and are picked up by the arithmetic solver.
        return true;
    }

    void theory_date::apply_sort_cnstr(enode * n, sort * s) {
        SASSERT(u.is_date(s));
        if (!is_attached_to_var(n)) {
            theory_var v = mk_var(n);
            ctx.attach_th_var(n, this, v);
        }
        ensure_axioms(n->get_expr());
    }

    void theory_date::display(std::ostream & out) const {
        out << "theory_date:\n";
        for (expr* e : m_axiomatized)
            out << mk_pp(e, m) << "\n";
    }

    void theory_date::init_model(model_generator & mg) {
        m_factory = alloc(date_factory, m, get_family_id());
        mg.register_factory(m_factory);
    }

    namespace {
        class date_value_proc : public model_value_proc {
            date_util&    u;
            date_factory& fct;
            enode*        m_year;
            enode*        m_month;
            enode*        m_day;
        public:
            date_value_proc(date_util& u, date_factory& fct, enode* y, enode* mo, enode* d):
                u(u), fct(fct), m_year(y), m_month(mo), m_day(d) {}

            void get_dependencies(buffer<model_value_dependency> & result) override {
                result.push_back(model_value_dependency(m_year));
                result.push_back(model_value_dependency(m_month));
                result.push_back(model_value_dependency(m_day));
            }

            app * mk_value(model_generator & mg, expr_ref_vector const & values) override {
                arith_util a(u.get_manager());
                rational y, mo, d;
                if (!a.is_numeral(values[0], y) ||
                    !a.is_numeral(values[1], mo) ||
                    !a.is_numeral(values[2], d) ||
                    !date_util::is_valid_date(y, mo, d)) {
                    // the validity axioms make this unreachable; stay safe
                    y = rational(1970); mo = rational(1); d = rational(1);
                }
                app* val = u.mk_date_value(y, mo, d);
                fct.add_trail(val);
                fct.register_value(val);
                return val;
            }
        };
    }

    model_value_proc * theory_date::mk_value(enode * n, model_generator & mg) {
        SASSERT(u.is_date(n->get_expr()));
        // search the class for a concrete date value or a member whose
        // selector terms have been internalized
        enode* yn = nullptr, *mon = nullptr, *dn = nullptr;
        rational y, mo, d;
        for (enode* sib : *n) {
            expr* se = sib->get_expr();
            if (u.is_date_value(se, y, mo, d)) {
                m_factory->register_value(se);
                return alloc(expr_wrapper_proc, to_app(se));
            }
            if (!yn) {
                app* y1  = u.mk_year(se);
                app* mo1 = u.mk_month(se);
                app* d1  = u.mk_day(se);
                if (ctx.e_internalized(y1) && ctx.e_internalized(mo1) && ctx.e_internalized(d1)) {
                    yn  = ctx.get_enode(y1);
                    mon = ctx.get_enode(mo1);
                    dn  = ctx.get_enode(d1);
                }
            }
        }
        if (yn)
            return alloc(date_value_proc, u, *m_factory, yn, mon, dn);
        // unconstrained date; any valid date will do
        app* val = to_app(m_factory->get_some_value(n->get_expr()->get_sort()));
        return alloc(expr_wrapper_proc, val);
    }
}
