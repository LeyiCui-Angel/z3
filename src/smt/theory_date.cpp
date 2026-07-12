/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Theory solver for calendar dates.

Author:

    Date theory extension 2026-07-05

--*/
#include "smt/theory_date.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "ast/ast_pp.h"

namespace smt {

    /**
       \brief Value factory for the Date sort. Fresh values enumerate
       successive epoch days starting from 1970-01-01.
    */
    class date_factory : public value_factory {
        date_util m_util;
        rational  m_next_epoch;
    public:
        date_factory(ast_manager& m, family_id fid):
            value_factory(m, fid),
            m_util(m),
            m_next_epoch(0) {}

        expr* get_some_value(sort* s) override {
            return m_util.mk_date(rational(1), rational(1), rational(1));
        }

        bool get_some_values(sort* s, expr_ref& v1, expr_ref& v2) override {
            v1 = m_util.mk_date(rational(1), rational(1), rational(1));
            v2 = m_util.mk_date(rational(1), rational(1), rational(2));
            return true;
        }

        expr* get_fresh_value(sort* s) override {
            rational y, mo, d;
            date_util::civil_of_epoch(m_next_epoch, y, mo, d);
            m_next_epoch += rational(1);
            return m_util.mk_date(y, mo, d);
        }

        void register_value(expr* n) override {}
    };

    class date_value_proc : public model_value_proc {
        date_util&                      m_util;
        svector<model_value_dependency> m_deps;
    public:
        date_value_proc(date_util& u, enode* y, enode* mo, enode* d): m_util(u) {
            m_deps.push_back(model_value_dependency(y));
            m_deps.push_back(model_value_dependency(mo));
            m_deps.push_back(model_value_dependency(d));
        }

        void get_dependencies(buffer<model_value_dependency>& result) override {
            result.append(m_deps.size(), m_deps.data());
        }

        app* mk_value(model_generator& mg, expr_ref_vector const& values) override {
            SASSERT(values.size() == 3);
            return m_util.mk_date(values[0], values[1], values[2]);
        }
    };

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        m_util(m),
        m_rewrite(m),
        m_atoms(m),
        m_rhs(m),
        m_prefs(m),
        m_generated_refs(m) {
        // normalize arithmetic atoms into "term <= numeral" form; the
        // arithmetic solver does not handle other inequality shapes
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_rewrite.updt_params(p);
    }

    theory_var theory_date::mk_th_var(enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        theory_var v = theory::mk_var(n);
        ctx.attach_th_var(n, this, v);
        ctx.mark_as_relevant(n);
        return v;
    }

    void theory_date::queue_axiom(expr* e) {
        queue_equiv(nullptr, e);
    }

    // for axioms already in final form, which simplification would fold away
    // (e.g. selector equations on concrete constructor applications)
    void theory_date::queue_no_rewrite(expr* e) {
        queue_equiv(e, m.mk_true());
    }

    void theory_date::queue_equiv(expr* atom, expr* rhs) {
        m_atoms.push_back(atom);
        ctx.push_trail(push_back_vector<expr_ref_vector>(m_atoms));
        m_rhs.push_back(rhs);
        ctx.push_trail(push_back_vector<expr_ref_vector>(m_rhs));
    }

    /**
       \brief Queue the redundant epoch envelope for date term e, once per
       term. Instantiated wherever an epoch-day tower over e's selectors is
       materialized (comparisons, date.add/date.sub, disequalities): it
       anchors the tower linearly to the year selector, without which
       integer branch-and-bound diverges once several towers coexist.
    */
    void theory_date::queue_envelope(expr* e) {
        rational y, mo, d;
        if (m_util.is_concrete_date(e, y, mo, d))
            return;
        if (m_enveloped.contains(e))
            return;
        m_enveloped.insert(e);
        ctx.push_trail(insert_obj_trail<expr>(m_enveloped, e));
        queue_axiom(m_util.mk_epoch_envelope(e));
    }

    /**
       \brief Queue the year-range preference atoms for date term e. They
       are internalized (not asserted) with the true-first decision flag:
       the search tries 1 <= year <= 9999 before falling back to the rest
       of the unbounded integer domain, so satisfiable instances yield
       models with human-scale years whenever such a model exists.
    */
    void theory_date::queue_year_prefs(expr* e) {
        rational y, mo, d;
        if (m_util.is_concrete_date(e, y, mo, d))
            return;
        expr_ref lo(m), hi(m), wlo(m), whi(m);
        m_util.mk_year_prefs(e, lo, hi);
        m_util.mk_year_prefs_wide(e, wlo, whi);
        for (expr* p : { lo.get(), hi.get(), wlo.get(), whi.get() }) {
            m_prefs.push_back(p);
            ctx.push_trail(push_back_vector<expr_ref_vector>(m_prefs));
        }
    }

    literal theory_date::mk_literal(expr* e) {
        ctx.internalize(e, false);
        literal lit = ctx.get_literal(e);
        ctx.mark_as_relevant(lit);
        return lit;
    }

    void theory_date::assert_axiom(expr* atom, expr* rhs) {
        // normalize the asserted formula; the theory solvers (notably
        // arithmetic) expect atoms in simplified form. The date atom of an
        // equivalence is kept as is: the rewriter could change gt/ge atoms
        // into their lt/le mirror.
        expr_ref r(rhs, m);
        m_rewrite(r);
        TRACE(date, tout << "assert: " << mk_pp(atom, m) << " == " << r << "\n";);
        if (!atom) {
            if (m.is_true(r))
                return;
            literal lit = mk_literal(r);
            ctx.mk_th_axiom(get_id(), 1, &lit);
            return;
        }
        literal alit = mk_literal(atom);
        if (m.is_true(r)) {
            ctx.mk_th_axiom(get_id(), 1, &alit);
            return;
        }
        if (m.is_false(r)) {
            literal nlit = ~alit;
            ctx.mk_th_axiom(get_id(), 1, &nlit);
            return;
        }
        literal rlit = mk_literal(r);
        ctx.mk_th_axiom(get_id(), ~alit, rlit);
        ctx.mk_th_axiom(get_id(), alit, ~rlit);
    }

    /**
       \brief The axioms constrain a term through its selector applications.
       If the term is not in rewriter normal form, the rewriting pass over
       the axioms would displace the selectors onto the normal form, leaving
       the original term unconstrained. Instead, link the term to its normal
       form (which then receives the axioms) with a plain equality.
       Returns true if the term was linked.
    */
    bool theory_date::link_normal_form(expr* e) {
        expr_ref norm(e, m);
        m_rewrite(norm);
        if (norm == e)
            return false;
        if (!m_linked.contains(e)) {
            m_linked.insert(e);
            ctx.push_trail(insert_obj_trail<expr>(m_linked, e));
            queue_no_rewrite(m.mk_eq(e, norm));
        }
        return true;
    }

    /**
       \brief Instantiate the axioms shared by every term of sort Date:
       validity of the selector triple, the reconstruction identity, and
       the epoch-day link.
    */
    void theory_date::add_date_term_axioms(expr* e) {
        if (m_term_axiomatized.contains(e) || m_generated.contains(e))
            return;
        m_term_axiomatized.insert(e);
        ctx.push_trail(insert_obj_trail<expr>(m_term_axiomatized, e));
        if (link_normal_form(e))
            return;
        expr_ref_vector axioms(m);
        expr_ref recon(m);
        m_util.mk_date_term_axioms(e, axioms, recon);
        // the reconstruction term is definitionally equal to e; do not
        // instantiate date-term axioms for it again
        if (!m_generated.contains(recon)) {
            m_generated.insert(recon);
            m_generated_refs.push_back(recon);
        }
        for (expr* ax : axioms)
            queue_axiom(ax);
        queue_year_prefs(e);
    }

    bool theory_date::internalize_atom(app * atom, bool gate_ctx) {
        SASSERT(m_util.is_lt(atom) || m_util.is_le(atom) || m_util.is_gt(atom) || m_util.is_ge(atom));
        for (expr* arg : *atom)
            mk_th_var(ensure_enode(arg));
        if (!ctx.b_internalized(atom)) {
            bool_var bv = ctx.mk_bool_var(atom);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }
        if (!m_op_axiomatized.contains(atom)) {
            m_op_axiomatized.insert(atom);
            ctx.push_trail(insert_obj_trail<expr>(m_op_axiomatized, atom));
            // gt/ge atoms are linked to their lt/le mirror instead
            if (!link_normal_form(atom))
                queue_equiv(atom, m_util.mk_compare_rhs(atom));
        }
        return true;
    }

    bool theory_date::internalize_term(app * term) {
        for (expr* arg : *term)
            ensure_enode(arg);
        enode* e = ctx.e_internalized(term) ? ctx.get_enode(term) : ctx.mk_enode(term, false, false, true);
        mk_th_var(e);
        if (!m_op_axiomatized.contains(term) && !m_generated.contains(term)) {
            m_op_axiomatized.insert(term);
            ctx.push_trail(insert_obj_trail<expr>(m_op_axiomatized, term));
            if (link_normal_form(term))
                ;
            else if (m_util.is_mk(term)) {
                expr_ref_vector axioms(m);
                bool concrete = m_util.mk_constructor_axioms(term, axioms);
                for (expr* ax : axioms)
                    concrete ? queue_no_rewrite(ax) : queue_axiom(ax);
            }
            else if (m_util.is_add(term) || m_util.is_sub(term)) {
                bool concrete = false, uses_epoch = false;
                expr_ref ax = m_util.mk_add_axiom(term, concrete, uses_epoch);
                concrete ? queue_no_rewrite(ax) : queue_axiom(ax);
                // eager selector injectivity between the result and its
                // base; resolves identities such as date.add(d,0,0,0) = d
                // at the boolean level
                queue_axiom(m_util.mk_diseq_axiom(term, term->get_arg(0)));
                if (uses_epoch) {
                    queue_envelope(term);
                    queue_envelope(term->get_arg(0));
                }
            }
        }
        return true;
    }

    void theory_date::apply_sort_cnstr(enode * n, sort * s) {
        SASSERT(m_util.is_date(s));
        mk_th_var(n);
        add_date_term_axioms(n->get_expr());
    }

    void theory_date::new_diseq_eh(theory_var v1, theory_var v2) {
        expr* e1 = get_enode(v1)->get_expr();
        expr* e2 = get_enode(v2)->get_expr();
        if (!m_util.is_date(e1))
            return;
        queue_axiom(m_util.mk_diseq_axiom(e1, e2));
    }

    void theory_date::propagate() {
        if (m_qhead < m_rhs.size()) {
            ctx.push_trail(value_trail<unsigned>(m_qhead));
            for (; m_qhead < m_rhs.size() && !ctx.inconsistent(); ++m_qhead) {
                expr_ref atom(m_atoms.get(m_qhead), m);
                expr_ref rhs(m_rhs.get(m_qhead), m);
                assert_axiom(atom, rhs);
            }
        }
        if (m_pref_qhead < m_prefs.size() && !ctx.inconsistent()) {
            ctx.push_trail(value_trail<unsigned>(m_pref_qhead));
            for (; m_pref_qhead < m_prefs.size() && !ctx.inconsistent(); ++m_pref_qhead) {
                expr_ref p(m_prefs.get(m_pref_qhead), m);
                literal l = mk_literal(p);
                // preference only: bias the case split toward the bounded
                // region; never asserted, so no model is excluded
                if (!l.sign())
                    ctx.set_true_first_flag(l.var());
            }
        }
    }

    void theory_date::display(std::ostream & out) const {
        out << "theory date:\n";
        display_var2enode(out);
    }

    void theory_date::init_model(model_generator & mg) {
        m_factory = alloc(date_factory, m, get_family_id());
        mg.register_factory(m_factory);
    }

    model_value_proc * theory_date::mk_value(enode * n, model_generator & mg) {
        SASSERT(m_util.is_date(n->get_expr()));
        // find a member of the class whose selector terms are internalized
        enode* it = n;
        do {
            expr* e = it->get_expr();
            app_ref y(m_util.mk_year(e), m), mo(m_util.mk_month(e), m), d(m_util.mk_day(e), m);
            if (ctx.e_internalized(y) && ctx.e_internalized(mo) && ctx.e_internalized(d))
                return alloc(date_value_proc, m_util, ctx.get_enode(y), ctx.get_enode(mo), ctx.get_enode(d));
            it = it->get_next();
        }
        while (it != n);
        return alloc(expr_wrapper_proc, m_util.mk_date(rational(1), rational(1), rational(1)));
    }

}
