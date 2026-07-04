/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Theory solver for calendar dates (legacy SMT core).

Author:

    Claude (Anthropic) 2026-07-04

--*/
#include "ast/ast_pp.h"
#include "smt/theory_date.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_arith_value.h"

namespace smt {

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        m_util(ctx.get_manager()),
        m_arith(ctx.get_manager()),
        m_rewrite(ctx.get_manager()) {
        // theory_lra expects atoms of the form (<= t numeral); have the
        // rewriter normalize the date axioms accordingly (as theory_fpa does)
        params_ref p;
        p.set_bool("arith_lhs", true);
        m_rewrite.updt_params(p);
    }

    theory_var theory_date::mk_th_var(enode* n) {
        theory_var v = n->get_th_var(get_id());
        if (v == null_theory_var) {
            v = theory::mk_var(n);
            ctx.attach_th_var(n, this, v);
        }
        return v;
    }

    void theory_date::assert_axiom(expr* fml) {
        expr_ref f(fml, m);
        m_rewrite(f);
        if (m.is_true(f))
            return;
        ctx.internalize(f, false);
        literal lit = ctx.get_literal(f);
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }

    void theory_date::ensure_axioms(expr* t) {
        SASSERT(is_date(t));
        if (m_axiomatized.contains(t))
            return;
        m_axiomatized.insert(t);
        ctx.push_trail(insert_obj_trail<expr>(m_axiomatized, t));
        m_terms.push_back(t);
        ctx.push_trail(push_back_vector<ptr_vector<expr>>(m_terms));
        if (u().is_add(t) || u().is_sub(t))
            ensure_axioms(to_app(t)->get_arg(0));
        // the selector terms hold the components in the model; make sure
        // they are internalized and relevant so that model construction
        // can depend on them
        expr_ref sels[3] = { expr_ref(u().mk_year(t), m), expr_ref(u().mk_month(t), m), expr_ref(u().mk_day(t), m) };
        for (expr_ref const& se : sels) {
            if (!ctx.e_internalized(se))
                ctx.internalize(se, false);
            ctx.mark_as_relevant(ctx.get_enode(se));
        }
        rational vy, vm, vd;
        if (u().eval_ground(t, vy, vm, vd)) {
            // Concretely evaluated term: assert the exact component values
            // without simplification. The rewriter would fold the selector
            // applications away, losing the egraph link between the term
            // and its components.
            assert_eq_axiom(u().mk_year(t), m_arith.mk_int(vy));
            assert_eq_axiom(u().mk_month(t), m_arith.mk_int(vm));
            assert_eq_axiom(u().mk_day(t), m_arith.mk_int(vd));
            assert_eq_axiom(u().mk_epoch_term(t), m_arith.mk_int(date_util::civil_to_days(vy, vm, vd)));
            return;
        }
        expr_ref_vector fmls(m);
        u().mk_term_spec(t, fmls);
        for (expr* f : fmls)
            assert_axiom(f);
    }

    void theory_date::assert_eq_axiom(expr* a, expr* b) {
        literal lit = mk_eq(a, b, false);
        ctx.mark_as_relevant(lit);
        ctx.mk_th_axiom(get_id(), 1, &lit);
    }

    void theory_date::internalize_cmp(literal lit, app* atom) {
        decl_kind k = atom->get_decl()->get_decl_kind();
        expr* a = atom->get_arg(0), *b = atom->get_arg(1);
        expr_ref spec = u().mk_cmp_spec(k, a, b);
        m_rewrite(spec);
        if (m.is_true(spec)) {
            ctx.mk_th_axiom(get_id(), 1, &lit);
            return;
        }
        if (m.is_false(spec)) {
            literal nlit = ~lit;
            ctx.mk_th_axiom(get_id(), 1, &nlit);
            return;
        }
        literal slit = mk_literal(spec);
        ctx.mark_as_relevant(slit);
        ctx.mk_th_axiom(get_id(), ~lit, slit);
        ctx.mk_th_axiom(get_id(), lit, ~slit);
        // redundant lexicographic definition; see date_util::mk_cmp_lex_spec
        expr_ref lex = u().mk_cmp_lex_spec(k, a, b);
        m_rewrite(lex);
        if (m.is_true(lex) || m.is_false(lex))
            return;
        literal llit = mk_literal(lex);
        ctx.mark_as_relevant(llit);
        ctx.mk_th_axiom(get_id(), ~lit, llit);
        ctx.mk_th_axiom(get_id(), lit, ~llit);
    }

    bool theory_date::internalize_atom(app* atom, bool gate_ctx) {
        SASSERT(u().is_comparison(atom));
        for (expr* arg : *atom) {
            ctx.internalize(arg, false);
            mk_th_var(ctx.get_enode(arg));
            ensure_axioms(arg);
        }
        bool_var bv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(bv, get_id());
        ctx.mark_as_relevant(bv);
        internalize_cmp(literal(bv, false), atom);
        return true;
    }

    bool theory_date::internalize_term(app* term) {
        for (expr* arg : *term)
            ctx.internalize(arg, false);
        enode* e = ctx.e_internalized(term) ? ctx.get_enode(term) : ctx.mk_enode(term, false, false, true);
        mk_th_var(e);
        if (is_date(term))
            ensure_axioms(term);
        else {
            // selector or epoch term: its date argument carries the axioms
            SASSERT(u().is_year(term) || u().is_month(term) || u().is_day(term) || u().is_epoch(term));
            ensure_axioms(term->get_arg(0));
        }
        return true;
    }

    void theory_date::apply_sort_cnstr(enode* n, sort* s) {
        SASSERT(m_util.is_date(s));
        mk_th_var(n);
        ensure_axioms(n->get_expr());
    }

    bool theory_date::get_component_values(expr* t, rational& y, rational& mo, rational& d) {
        arith_value av(m);
        av.init(&ctx);
        expr_ref ye(u().mk_year(t), m), me(u().mk_month(t), m), de(u().mk_day(t), m);
        return
            ctx.e_internalized(ye) && av.get_value(ye, y) &&
            ctx.e_internalized(me) && av.get_value(me, mo) &&
            ctx.e_internalized(de) && av.get_value(de, d);
    }

    final_check_status theory_date::final_check_eh(unsigned level) {
        // Extensionality: two date terms whose components agree in the
        // arithmetic model must be equal. Instantiate the extensionality
        // lemma for any pair of candidate terms found in distinct classes.
        bool added = false;
        obj_map<enode, expr*> root2term;
        for (expr* t : m_terms) {
            if (!ctx.e_internalized(t))
                continue;
            enode* r = ctx.get_enode(t)->get_root();
            if (!root2term.contains(r))
                root2term.insert(r, t);
        }
        ptr_vector<expr> reps;
        for (auto const& kv : root2term)
            reps.push_back(kv.m_value);
        for (unsigned i = 0; i < reps.size() && !ctx.inconsistent(); ++i) {
            rational y1, m1, d1;
            if (!get_component_values(reps[i], y1, m1, d1))
                continue;
            for (unsigned j = i + 1; j < reps.size() && !ctx.inconsistent(); ++j) {
                rational y2, m2, d2;
                if (!get_component_values(reps[j], y2, m2, d2))
                    continue;
                if (y1 != y2 || m1 != m2 || d1 != d2)
                    continue;
                expr* a = reps[i], *b = reps[j];
                literal eq_y = mk_eq(u().mk_year(a), u().mk_year(b), false);
                literal eq_m = mk_eq(u().mk_month(a), u().mk_month(b), false);
                literal eq_d = mk_eq(u().mk_day(a), u().mk_day(b), false);
                literal eq   = mk_eq(a, b, false);
                literal lits[4] = { ~eq_y, ~eq_m, ~eq_d, eq };
                ctx.mk_th_axiom(get_id(), 4, lits);
                added = true;
            }
        }
        return added ? FC_CONTINUE : FC_DONE;
    }

    void theory_date::display(std::ostream& out) const {
        out << "theory date:\n";
        for (expr* t : m_terms)
            out << mk_bounded_pp(t, m, 2) << "\n";
    }

    void theory_date::init_model(model_generator& mg) {
        m_factory = alloc(date_factory, m, get_family_id());
        mg.register_factory(m_factory);
    }

    class date_value_proc : public model_value_proc {
        theory_date&    m_th;
        enode*          m_year;
        enode*          m_month;
        enode*          m_day;
    public:
        date_value_proc(theory_date& th, enode* y, enode* mo, enode* d):
            m_th(th), m_year(y), m_month(mo), m_day(d) {}

        void get_dependencies(buffer<model_value_dependency>& result) override {
            result.push_back(model_value_dependency(m_year));
            result.push_back(model_value_dependency(m_month));
            result.push_back(model_value_dependency(m_day));
        }

        app* mk_value(model_generator& mg, expr_ref_vector const& values) override {
            arith_util a(m_th.get_manager());
            rational y, mo, d;
            if (values.size() == 3 &&
                a.is_numeral(values[0], y) && a.is_numeral(values[1], mo) && a.is_numeral(values[2], d) &&
                date_util::is_valid_date(y, mo, d)) {
                app* val = m_th.m_util.mk_date(y, mo, d);
                if (m_th.m_factory)
                    m_th.m_factory->register_value(val);
                return val;
            }
            return to_app(m_th.m_factory->get_some_value(m_th.m_util.mk_date_sort()));
        }
    };

    model_value_proc* theory_date::mk_value(enode* n, model_generator& mg) {
        // find a class member whose selector terms have been internalized
        enode* it = n;
        do {
            expr* t = it->get_expr();
            if (m_axiomatized.contains(t)) {
                expr_ref ye(u().mk_year(t), m), me(u().mk_month(t), m), de(u().mk_day(t), m);
                if (ctx.e_internalized(ye) && ctx.e_internalized(me) && ctx.e_internalized(de))
                    return alloc(date_value_proc, *this, ctx.get_enode(ye), ctx.get_enode(me), ctx.get_enode(de));
            }
            it = it->get_next();
        }
        while (it != n);
        return alloc(expr_wrapper_proc, to_app(m_factory->get_some_value(m_util.mk_date_sort())));
    }

}
