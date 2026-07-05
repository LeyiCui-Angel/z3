/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Theory solver for calendar dates (legacy SMT pipeline).

Author:

    Claude 2026-07-05

--*/
#include "ast/ast_pp.h"
#include "model/value_factory.h"
#include "smt/theory_date.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"

namespace smt {

    // Produces calendar-valid date values, enumerated by Rata Die day number.
    class date_factory : public value_factory {
        date_util           dt;
        obj_hashtable<expr> m_values;
        ast_ref_vector      m_trail;
        rational            m_next_rd;

        app* mk_rd(rational const& rd) {
            rational y, mo, d;
            date_decl_plugin::date_of_rata_die(rd, y, mo, d);
            return dt.mk_date(y, mo, d);
        }

    public:
        date_factory(ast_manager& m, family_id fid):
            value_factory(m, fid),
            dt(m),
            m_trail(m),
            m_next_rd(1) {
        }

        expr* get_some_value(sort* s) override {
            return mk_rd(rational(1));
        }

        bool get_some_values(sort* s, expr_ref& v1, expr_ref& v2) override {
            v1 = mk_rd(rational(1));
            v2 = mk_rd(rational(2));
            return true;
        }

        expr* get_fresh_value(sort* s) override {
            app* r;
            do {
                r = mk_rd(m_next_rd);
                m_next_rd += 1;
            }
            while (m_values.contains(r));
            register_value(r);
            return r;
        }

        void register_value(expr* n) override {
            if (!m_values.contains(n)) {
                m_values.insert(n);
                m_trail.push_back(n);
            }
        }
    };

    // Builds the value of a Date term from the values of its selector terms.
    class theory_date::date_value_proc : public model_value_proc {
        theory_date& th;
        enode*       m_year;
        enode*       m_month;
        enode*       m_day;

    public:
        date_value_proc(theory_date& th, enode* y, enode* mo, enode* d):
            th(th), m_year(y), m_month(mo), m_day(d) {
        }

        void get_dependencies(buffer<model_value_dependency>& result) override {
            result.push_back(model_value_dependency(m_year));
            result.push_back(model_value_dependency(m_month));
            result.push_back(model_value_dependency(m_day));
        }

        app* mk_value(model_generator& mg, expr_ref_vector const& values) override {
            rational y, mo, d;
            if (values.size() == 3 &&
                th.a.is_numeral(values[0], y) &&
                th.a.is_numeral(values[1], mo) &&
                th.a.is_numeral(values[2], d) &&
                date_decl_plugin::is_valid_date(y, mo, d))
                return th.dt.mk_date(y, mo, d);
            // The validity axioms guarantee well-formed selector values;
            // fall back to an arbitrary date if they are unavailable.
            return th.dt.mk_date(rational(1), rational(1), rational(1));
        }
    };

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        dt(ctx.get_manager()),
        a(ctx.get_manager()),
        ax(ctx.get_manager()),
        m_axioms(ctx.get_manager()),
        m_dates(ctx.get_manager()) {
    }

    void theory_date::push_axiom(expr* e) {
        // The axiom is asserted as constructed: simplifying it here could
        // rewrite away the date terms it is meant to constrain (e.g.
        // (date.add d 0 0 0) folds to d), detaching the axiom from the
        // enodes of the original goal.
        m_axioms.push_back(e);
    }

    enode* theory_date::ensure_enode(app* term) {
        for (expr* arg : *term)
            ctx.internalize(arg, false);
        enode* e = ctx.e_internalized(term) ? ctx.get_enode(term) : ctx.mk_enode(term, false, m().is_bool(term), true);
        if (dt.is_date(term) && !is_attached_to_var(e)) {
            theory_var v = mk_var(e);
            ctx.attach_th_var(e, this, v);
        }
        return e;
    }

    void theory_date::add_date_term(app* term) {
        SASSERT(dt.is_date(term));
        ensure_enode(term);
        if (m_seen.contains(term))
            return;
        m_seen.insert(term);
        // Every Date term denotes a calendar-valid date ...
        push_axiom(ax.valid_axiom(term));
        // ... and is reconstructed from its selectors. Direct date.mk
        // applications are excluded: on valid arguments reconstruction
        // follows from the selector axioms, and instantiating it on
        // syntactically new date.mk terms would not terminate.
        if (!dt.is_mk(term))
            push_axiom(ax.recon_axiom(term));
        // Defining axioms of the date operations.
        if (dt.is_mk(term))
            push_axiom(ax.mk_axiom(term));
        else if (dt.is_add(term) || dt.is_sub(term)) {
            push_axiom(ax.add_axiom(term));
            if (is_app(term->get_arg(0)))
                add_date_term(to_app(term->get_arg(0)));
        }
        // Equality and order agree with the Rata Die day numbers.
        for (expr* other : m_dates)
            push_axiom(ax.bridge_axiom(term, other));
        m_dates.push_back(term);
    }

    bool theory_date::internalize_atom(app* atom, bool gate_ctx) {
        SASSERT(dt.is_lt(atom) || dt.is_le(atom) || dt.is_gt(atom) || dt.is_ge(atom));
        if (ctx.b_internalized(atom))
            return true;
        for (expr* arg : *atom)
            ctx.internalize(arg, false);
        literal l(ctx.mk_bool_var(atom));
        ctx.set_var_theory(l.var(), get_id());
        for (expr* arg : *atom)
            if (is_app(arg))
                add_date_term(to_app(arg));
        push_axiom(ax.cmp_axiom(atom));
        return true;
    }

    bool theory_date::internalize_term(app* term) {
        ensure_enode(term);
        switch (term->get_decl_kind()) {
        case OP_DATE_MK:
        case OP_DATE_ADD:
        case OP_DATE_SUB:
            add_date_term(term);
            break;
        case OP_DATE_YEAR:
        case OP_DATE_MONTH:
        case OP_DATE_DAY:
            if (is_app(term->get_arg(0)))
                add_date_term(to_app(term->get_arg(0)));
            break;
        default:
            break;
        }
        return true;
    }

    void theory_date::apply_sort_cnstr(enode* n, sort* s) {
        SASSERT(dt.is_date(s));
        if (is_app(n->get_expr()))
            add_date_term(to_app(n->get_expr()));
    }

    bool theory_date::can_propagate() {
        return m_axioms_qhead < m_axioms.size();
    }

    void theory_date::propagate() {
        if (m_axioms_qhead == m_axioms.size())
            return;
        ctx.push_trail(value_trail(m_axioms_qhead));
        for (; m_axioms_qhead < m_axioms.size(); ++m_axioms_qhead) {
            expr* e = m_axioms.get(m_axioms_qhead);
            TRACE(theory_date, tout << "assert: " << mk_pp(e, m()) << "\n";);
            if (m().has_trace_stream())
                log_axiom_instantiation(e);
            ctx.internalize(e, false);
            if (m().has_trace_stream())
                m().trace_stream() << "[end-of-instance]\n";
            literal lit(ctx.get_literal(e));
            ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), 1, &lit);
        }
    }

    void theory_date::init_model(model_generator& mg) {
        mg.register_factory(alloc(date_factory, m(), get_family_id()));
    }

    model_value_proc* theory_date::mk_value(enode* n, model_generator& mg) {
        // Locate internalized selector terms for some expression in the class.
        for (enode* sib : *n) {
            expr* e = sib->get_expr();
            app_ref y(dt.mk_year(e), m()), mo(dt.mk_month(e), m()), d(dt.mk_day(e), m());
            if (ctx.e_internalized(y) && ctx.e_internalized(mo) && ctx.e_internalized(d))
                return alloc(date_value_proc, *this, ctx.get_enode(y), ctx.get_enode(mo), ctx.get_enode(d));
        }
        return alloc(expr_wrapper_proc, dt.mk_date(rational(1), rational(1), rational(1)));
    }

    void theory_date::display(std::ostream& out) const {
        out << "theory_date:\n";
        for (expr* d : m_dates)
            out << mk_pp(d, m()) << "\n";
    }

    theory* mk_theory_date(context& ctx) { return alloc(theory_date, ctx); }
}
