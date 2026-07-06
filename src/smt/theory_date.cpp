/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Theory solver for the Dates theory in the legacy SMT core.

Author:

    Date theory extension 2026-07-04

--*/
#include "smt/theory_date.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"

namespace smt {

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        dt(m),
        a(m),
        m_ax(m),
        m_rw(m) {
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_rw.updt_params(p);
        m_ax.set_add_axiom([this](expr* e) { assert_axiom(e); });
        m_ax.set_add_eq([this](expr* a, expr* b) { assert_eq(a, b); });
        m_ax.set_add_iff([this](expr* atom, expr* def) { assert_iff(atom, def); });
    }

    void theory_date::assert_axiom(expr* e) {
        expr_ref fml(e, m);
        // normalize arithmetic atoms into the form the arithmetic
        // solver internalizes
        m_rw(fml);
        if (m.is_true(fml))
            return;
        TRACE(date, tout << "assert: " << fml << "\n";);
        literal l = mk_literal(fml);
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), 1, &l);
    }

    // Definitional equality. Both sides are internalized verbatim: the
    // left-hand side anchors selector and epoch terms of a Date e-graph
    // node, so it must not be folded by the rewriter.
    void theory_date::assert_eq(expr* a, expr* b) {
        // normalize embedded arithmetic atoms on the definition side only
        expr_ref bn(b, m);
        m_rw(bn);
        TRACE(date, tout << "assert: " << mk_pp(a, m) << " = " << bn << "\n";);
        literal l = mk_eq(a, bn, false);
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), 1, &l);
    }

    // Definition of a comparison atom. The atom keeps its literal; only
    // the definition side is normalized.
    void theory_date::assert_iff(expr* atom, expr* def) {
        expr_ref d(def, m);
        m_rw(d);
        TRACE(date, tout << "assert: " << mk_pp(atom, m) << " <=> " << d << "\n";);
        literal la = mk_literal(atom);
        ctx.mark_as_relevant(la);
        if (m.is_true(d)) {
            ctx.mk_th_axiom(get_id(), 1, &la);
            return;
        }
        if (m.is_false(d)) {
            literal nla = ~la;
            ctx.mk_th_axiom(get_id(), 1, &nla);
            return;
        }
        literal ld = mk_literal(d);
        ctx.mark_as_relevant(ld);
        ctx.mk_th_axiom(get_id(), ~la, ld);
        ctx.mk_th_axiom(get_id(), la, ~ld);
    }

    // Track a Date-sorted enode: attach a theory variable (used for model
    // construction) and schedule its defining axioms.
    void theory_date::add_date_term(enode* n) {
        if (is_attached_to_var(n))
            return;
        SASSERT(dt.is_date(n->get_expr()));
        theory_var v = theory::mk_var(n);
        ctx.attach_th_var(n, this, v);
        ctx.mark_as_relevant(n);
        ctx.push_trail(push_back_vector(m_terms));
        m_terms.push_back(n->get_expr());
    }

    bool theory_date::internalize_term(app* term) {
        SASSERT(term->get_family_id() == get_id());
        for (expr* arg : *term)
            ctx.internalize(arg, false);
        enode* e = ctx.e_internalized(term) ? ctx.get_enode(term) :
            ctx.mk_enode(term, false, false, true);
        if (dt.is_date(term))
            add_date_term(e);
        else {
            // selector applications; the argument carries the axioms
            SASSERT(dt.is_selector(term));
            add_date_term(ctx.get_enode(term->get_arg(0)));
        }
        return true;
    }

    bool theory_date::internalize_atom(app* atom, bool gate_ctx) {
        SASSERT(dt.is_comparison(atom));
        for (expr* arg : *atom) {
            ctx.internalize(arg, false);
            add_date_term(ctx.get_enode(arg));
        }
        bool_var bv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(bv, get_id());
        ctx.mark_as_relevant(bv);
        ctx.push_trail(push_back_vector(m_atoms));
        m_atoms.push_back(atom);
        return true;
    }

    void theory_date::apply_sort_cnstr(enode* n, sort* s) {
        SASSERT(dt.is_date(s));
        add_date_term(n);
    }

    void theory_date::new_diseq_eh(theory_var v1, theory_var v2) {
        ctx.push_trail(push_back_vector(m_diseqs));
        m_diseqs.push_back({v1, v2});
    }

    bool theory_date::can_propagate() {
        return m_terms_qhead < m_terms.size() || m_atoms_qhead < m_atoms.size() ||
               m_diseqs_qhead < m_diseqs.size();
    }

    void theory_date::propagate() {
        flush_axioms();
    }

    // Instantiating axioms internalizes new terms, which can grow the
    // queues while they are drained; iterate until a fixed point.
    bool theory_date::flush_axioms() {
        bool advanced = false;
        while (can_propagate()) {
            advanced = true;
            if (m_terms_qhead < m_terms.size()) {
                ctx.push_trail(value_trail<unsigned>(m_terms_qhead));
                expr* t = m_terms[m_terms_qhead++];
                m_ax.term_axioms(t);
            }
            else if (m_atoms_qhead < m_atoms.size()) {
                ctx.push_trail(value_trail<unsigned>(m_atoms_qhead));
                app* p = m_atoms[m_atoms_qhead++];
                m_ax.compare_axioms(p);
            }
            else {
                ctx.push_trail(value_trail<unsigned>(m_diseqs_qhead));
                auto [v1, v2] = m_diseqs[m_diseqs_qhead++];
                m_ax.diseq_axiom(get_enode(v1)->get_expr(), get_enode(v2)->get_expr());
            }
        }
        return advanced;
    }

    final_check_status theory_date::final_check_eh(unsigned level) {
        return flush_axioms() ? FC_CONTINUE : FC_DONE;
    }

    void theory_date::display(std::ostream& out) const {
        out << "theory date:\n";
        for (unsigned v = 0; v < get_num_vars(); ++v)
            out << v << " -> " << enode_pp(get_enode(v), ctx) << "\n";
    }

    namespace {
        // Assemble (date.mk y m d) from the arithmetic model values of the
        // selector terms of a Date enode.
        class date_value_proc : public model_value_proc {
            date_util& dt;
            arith_util& a;
            enode* m_deps[3];
        public:
            date_value_proc(date_util& dt, arith_util& a, enode* y, enode* mo, enode* d):
                dt(dt), a(a), m_deps{ y, mo, d } {}

            void get_dependencies(buffer<model_value_dependency>& result) override {
                for (enode* n : m_deps)
                    result.push_back(model_value_dependency(n));
            }

            app* mk_value(model_generator& mg, expr_ref_vector const& values) override {
                rational num[3] = { rational(1), rational(1), rational(1) };
                for (unsigned i = 0; i < 3; ++i)
                    if (values.size() > i)
                        a.is_numeral(values[i], num[i]);
                return dt.mk_mk(num[0], num[1], num[2]);
            }
        };
    }

    model_value_proc* theory_date::mk_value(enode* n, model_generator& mg) {
        expr* t = n->get_expr();
        expr_ref y(dt.mk_year(t), m), mo(dt.mk_month(t), m), d(dt.mk_day(t), m);
        if (ctx.e_internalized(y) && ctx.e_internalized(mo) && ctx.e_internalized(d))
            return alloc(date_value_proc, dt, a,
                         ctx.get_enode(y), ctx.get_enode(mo), ctx.get_enode(d));
        // unconstrained date; any calendar-valid value works
        return alloc(expr_wrapper_proc, dt.mk_mk(rational(1), rational(1), rational(1)));
    }
}
