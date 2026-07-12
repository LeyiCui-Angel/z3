/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Theory solver for calendar dates (legacy SMT core).

Author:

    Z3 date theory extension 2026-07-05

--*/
#include "smt/theory_date.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "util/trail.h"

namespace smt {

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        u(m),
        a(m),
        m_rw(m),
        m_avalue(m),
        m_e1s(m),
        m_e2s(m) {
        // normalize every inequality to bound form (poly <= numeral):
        // theory axioms bypass the preprocessing pipeline, and
        // theory_lra::internalize_atom treats any other inequality shape
        // (e.g. an ite moved to the right-hand side) as unsupported,
        // which turns final check into FC_GIVEUP
        params_ref p;
        p.set_bool("arith_ineq_lhs", true);
        m_rw.updt_params(p);
    }

    void theory_date::ensure_var(enode* n) {
        if (!is_attached_to_var(n)) {
            theory_var v = theory::mk_var(n);
            ctx.attach_th_var(n, this, v);
            if (u.is_date(n->get_expr()))
                push_axiom(AX_EPOCH_BOUND, n->get_expr());
        }
    }

    // ------------------------------------------------------------------
    // deferred axiom queue.
    // internalization of date terms can occur nested within the
    // internalization of arithmetic atoms, so axioms (which create new
    // arithmetic terms) are queued and asserted from propagate().

    void theory_date::push_axiom(axiom_kind k, expr* e1, expr* e2) {
        m_kinds.push_back(k);
        m_e1s.push_back(e1);
        m_e2s.push_back(e2);
        ctx.push_trail(push_back_vector<svector<axiom_kind>>(m_kinds));
        ctx.push_trail(push_back_vector<expr_ref_vector>(m_e1s));
        ctx.push_trail(push_back_vector<expr_ref_vector>(m_e2s));
    }

    bool theory_date::flush_axioms() {
        if (m_qhead == m_kinds.size())
            return false;
        ctx.push_trail(value_trail<unsigned>(m_qhead));
        bool asserted = false;
        while (m_qhead < m_kinds.size() && !ctx.inconsistent()) {
            unsigned i = m_qhead++;
            asserted = true;
            switch (m_kinds[i]) {
            case AX_EQ:
                assert_eq_axiom(m_e1s.get(i), m_e2s.get(i));
                break;
            case AX_CMP:
                assert_cmp_axiom(to_app(m_e1s.get(i)));
                break;
            case AX_EPOCH_BOUND:
                assert_epoch_bound(m_e1s.get(i));
                break;
            case AX_INJ:
                assert_injectivity(m_e1s.get(i), m_e2s.get(i));
                break;
            case AX_COMPONENTS:
                assert_component_axioms(m_e1s.get(i));
                break;
            case AX_MK:
                assert_mk_axioms(to_app(m_e1s.get(i)));
                break;
            case AX_MKINJ:
                assert_mk_injectivity(m_e1s.get(i));
                break;
            }
        }
        return asserted;
    }

    void theory_date::assert_eq_axiom(expr* lhs, expr* rhs) {
        expr_ref _lhs(lhs, m), _rhs(rhs, m);
        m_rw(_rhs);
        if (_lhs == _rhs)
            return;
        literal l = mk_eq(_lhs, _rhs, false);
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), 1, &l);
    }

    void theory_date::assert_unit_axiom(expr* e) {
        expr_ref c(e, m);
        m_rw(c);
        if (m.is_true(c))
            return;
        if (m.is_false(c)) {
            literal fl = false_literal;
            ctx.mk_th_axiom(get_id(), 1, &fl);
            return;
        }
        literal l = mk_literal(c);
        ctx.mark_as_relevant(l);
        ctx.mk_th_axiom(get_id(), 1, &l);
    }

    void theory_date::assert_cmp_axiom(app* atom) {
        if (!ctx.b_internalized(atom))
            return;
        literal lit(ctx.get_bool_var(atom));
        expr* x = atom->get_arg(0);
        expr* y = atom->get_arg(1);
        expr_ref ep1(u.mk_epoch(x), m);
        expr_ref ep2(u.mk_epoch(y), m);
        // build bound-form atoms (term <= numeral): this is the normal form
        // the arithmetic solvers expect for theory-created literals
        expr_ref ineq(m);
        switch (atom->get_decl_kind()) {
        case OP_DATE_LT: ineq = a.mk_le(a.mk_sub(ep1, ep2), a.mk_int(-1)); break;
        case OP_DATE_LE: ineq = a.mk_le(a.mk_sub(ep1, ep2), a.mk_int(0)); break;
        case OP_DATE_GT: ineq = a.mk_le(a.mk_sub(ep2, ep1), a.mk_int(-1)); break;
        case OP_DATE_GE: ineq = a.mk_le(a.mk_sub(ep2, ep1), a.mk_int(0)); break;
        default: UNREACHABLE();
        }
        m_rw(ineq);
        if (m.is_true(ineq)) {
            ctx.mk_th_axiom(get_id(), 1, &lit);
            return;
        }
        if (m.is_false(ineq)) {
            literal nlit = ~lit;
            ctx.mk_th_axiom(get_id(), 1, &nlit);
            return;
        }
        literal ilit = mk_literal(ineq);
        ctx.mark_as_relevant(ilit);
        ctx.mk_th_axiom(get_id(), ~lit, ilit);
        ctx.mk_th_axiom(get_id(), lit, ~ilit);
    }

    /**
       \brief Assert the tautology (<= epoch(d) 0) or (>= epoch(d) 0).
       Its purpose is to register epoch(d) with the arithmetic solver, so
       that every date has an epoch value in the arithmetic model.
    */
    void theory_date::assert_epoch_bound(expr* d) {
        if (!ctx.e_internalized(d))
            return;
        expr_ref ep(u.mk_epoch(d), m);
        expr_ref zero(a.mk_int(0), m);
        literal le = mk_literal(a.mk_le(ep, zero));
        literal ge = mk_literal(a.mk_ge(ep, zero));
        ctx.mark_as_relevant(le);
        ctx.mark_as_relevant(ge);
        ctx.mk_th_axiom(get_id(), le, ge);
    }

    /**
       \brief epoch(a) = epoch(b) => a = b. Together with congruence for
       date.epoch! this makes the epoch map a bijection between dates and
       integers.
    */
    void theory_date::assert_injectivity(expr* d1, expr* d2) {
        if (!ctx.e_internalized(d1) || !ctx.e_internalized(d2))
            return;
        expr_ref ep1(u.mk_epoch(d1), m);
        expr_ref ep2(u.mk_epoch(d2), m);
        literal l_ep = mk_eq(ep1, ep2, false);
        literal l_d  = mk_eq(d1, d2, false);
        ctx.mark_as_relevant(l_ep);
        ctx.mark_as_relevant(l_d);
        ctx.mk_th_axiom(get_id(), ~l_ep, l_d);
    }

    /**
       \brief Component axioms for a Date term: its selector terms form a
       valid civil triple whose days-from-civil image is its epoch. The
       selectors act as the component variables of the relational
       encoding; the inverse civil-of-epoch direction is never encoded,
       the integer solver searches over the bounded components instead.
    */
    void theory_date::assert_component_axioms(expr* d) {
        if (!ctx.e_internalized(d))
            return;
        expr_ref y(u.mk_year(d), m);
        expr_ref mo(u.mk_month(d), m);
        expr_ref dd(u.mk_day(d), m);
        assert_unit_axiom(a.mk_ge(mo, a.mk_int(1)));
        assert_unit_axiom(a.mk_le(mo, a.mk_int(12)));
        assert_unit_axiom(a.mk_ge(dd, a.mk_int(1)));
        // bound form (term <= numeral): days-in-month is an ite term
        assert_unit_axiom(a.mk_le(a.mk_sub(dd, u.mk_days_in_month(y, mo)), a.mk_int(0)));
        expr_ref ep(u.mk_epoch(d), m);
        assert_eq_axiom(ep, u.mk_days_from_civil(y, mo, dd));
    }

    /**
       \brief Axioms for the strict constructor. The arguments must form a
       valid civil date: 1 <= m <= 12 and 1 <= d <= days-in-month(y, m);
       formulas that force date.mk onto out-of-range components are
       unsatisfiable. Under these constraints the epoch is defined by
       days-from-civil directly.
    */
    void theory_date::assert_mk_axioms(app* mk) {
        if (!ctx.e_internalized(mk))
            return;
        expr* y = mk->get_arg(0);
        expr* mo = mk->get_arg(1);
        expr* d = mk->get_arg(2);
        assert_unit_axiom(a.mk_ge(mo, a.mk_int(1)));
        assert_unit_axiom(a.mk_le(mo, a.mk_int(12)));
        assert_unit_axiom(a.mk_ge(d, a.mk_int(1)));
        // bound-form atom (term <= numeral): the normal form the
        // arithmetic solvers expect for theory-created literals
        assert_unit_axiom(a.mk_le(a.mk_sub(d, u.mk_days_in_month(y, mo)), a.mk_int(0)));
        expr_ref ep(u.mk_epoch(mk), m);
        assert_eq_axiom(ep, u.mk_days_from_civil(y, mo, d));
        // the components of the constructed date are the constructor
        // arguments. For ground constructors the definition above is
        // already a fixed epoch and the selector equalities are folded
        // by the rewriter wherever selectors occur.
        rational ry, rmo, rd;
        if (!u.is_numeral_mk(mk, ry, rmo, rd)) {
            assert_eq_axiom(y, u.mk_year(mk));
            assert_eq_axiom(mo, u.mk_month(mk));
            assert_eq_axiom(d, u.mk_day(mk));
        }
        // constructor-selector roundtrip fast-path
        if (u.is_year(y) && u.is_month(mo) && u.is_day(d)) {
            expr* x = to_app(y)->get_arg(0);
            if (x == to_app(mo)->get_arg(0) && x == to_app(d)->get_arg(0))
                assert_eq_axiom(ep, u.mk_epoch(x));
        }
    }

    /**
       \brief Components of dates are uniquely determined, so equal dates
       built by date.mk have equal constructor arguments. This gives the
       arithmetic solver the component equalities directly instead of
       requiring it to invert the days-from-civil map.
    */
    void theory_date::assert_mk_injectivity(expr* e) {
        if (!ctx.e_internalized(e))
            return;
        enode* n = ctx.get_enode(e);
        app* pivot = nullptr;
        for (enode* sib : *n->get_root()) {
            expr* s = sib->get_expr();
            if (!u.is_mk(s))
                continue;
            if (!pivot) {
                pivot = to_app(s);
                continue;
            }
            literal l_eq = mk_eq(pivot, s, false);
            ctx.mark_as_relevant(l_eq);
            for (unsigned i = 0; i < 3; ++i) {
                literal l_arg = mk_eq(pivot->get_arg(i), to_app(s)->get_arg(i), false);
                ctx.mark_as_relevant(l_arg);
                ctx.mk_th_axiom(get_id(), ~l_eq, l_arg);
            }
        }
    }

    // ------------------------------------------------------------------
    // internalization

    bool theory_date::internalize_atom(app* atom, bool gate_ctx) {
        SASSERT(u.is_lt(atom) || u.is_le(atom) || u.is_gt(atom) || u.is_ge(atom));
        for (expr* arg : *atom)
            ctx.internalize(arg, false);
        if (!ctx.b_internalized(atom)) {
            bool_var bv = ctx.mk_bool_var(atom);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }
        push_axiom(AX_CMP, atom);
        return true;
    }

    bool theory_date::internalize_term(app* term) {
        for (expr* arg : *term)
            ctx.internalize(arg, false);
        enode* e = ctx.e_internalized(term) ? ctx.get_enode(term) : ctx.mk_enode(term, false, false, true);
        // only Date-sorted terms carry a theory variable; Int-sorted date
        // terms (selectors, epochs) are glued to arithmetic by their axioms
        if (u.is_date(term))
            ensure_var(e);
        switch (term->get_decl_kind()) {
        case OP_DATE_MK:
            push_axiom(AX_MK, term);
            break;
        case OP_DATE_ADD:
        case OP_DATE_SUB: {
            // date.sub is date.add with negated offsets
            bool is_sub = term->get_decl_kind() == OP_DATE_SUB;
            expr* b = term->get_arg(0);
            expr_ref py(term->get_arg(1), m), pm(term->get_arg(2), m), pd(term->get_arg(3), m);
            if (is_sub) {
                py = u.mk_ineg(py);
                pm = u.mk_ineg(pm);
                pd = u.mk_ineg(pd);
            }
            if (u.is_zero_month_shift(py, pm)) {
                // pure day shift: the base date is a valid date, so the
                // month step and the day clamp are the identity and the
                // epoch shifts exactly
                push_axiom(AX_EQ, u.mk_epoch(term), a.mk_add(u.mk_epoch(b), pd));
            }
            else if (u.is_zero(pd)) {
                // pure month shift: the components of the result are
                // definable without division. On the absolute month
                // count 12*y + mo the shift is linear, and the bounds
                // 1 <= month <= 12 from the component axioms make the
                // year/month decomposition unique; the day is the base
                // day clamped to the target month length. The epoch
                // follows from the component axioms of the result.
                push_axiom(AX_COMPONENTS, term);
                if (!u.is_mk(b))
                    push_axiom(AX_COMPONENTS, b);
                expr_ref yb(u.mk_year(b), m), mb(u.mk_month(b), m), db(u.mk_day(b), m);
                expr_ref yt(u.mk_year(term), m), mt(u.mk_month(term), m);
                expr_ref shift(a.mk_add(a.mk_mul(a.mk_int(12), py), pm), m);
                push_axiom(AX_EQ, u.mk_month_total(yt, mt),
                           a.mk_add(u.mk_month_total(yb, mb), shift));
                push_axiom(AX_EQ, u.mk_day(term), u.mk_clamped_day(db, yt, mt));
            }
            else {
                // general shift: factor through the pure month shift,
                // then shift days exactly on epochs
                expr_ref zero(a.mk_int(0), m);
                expr* args[4] = { b, py, pm, zero };
                app_ref mid(m.mk_app(get_family_id(), OP_DATE_ADD, 4, args), m);
                push_axiom(AX_EQ, u.mk_epoch(term), a.mk_add(u.mk_epoch(mid), pd));
            }
            break;
        }
        case OP_DATE_YEAR:
        case OP_DATE_MONTH:
        case OP_DATE_DAY: {
            // the selector term itself is the component variable; for
            // date.mk arguments the constructor axioms already equate
            // the selectors with the arguments
            expr* b = term->get_arg(0);
            rational ry, rmo, rd;
            if (u.is_numeral_mk(b, ry, rmo, rd)) {
                // selectors of ground constructors are fixed (invalid
                // ground constructors force unsat through their own axioms)
                if (date_util::is_valid_civil(ry, rmo, rd)) {
                    rational v = term->get_decl_kind() == OP_DATE_YEAR ? ry :
                                 term->get_decl_kind() == OP_DATE_MONTH ? rmo : rd;
                    push_axiom(AX_EQ, term, a.mk_int(v));
                }
            }
            else if (!u.is_mk(b))
                push_axiom(AX_COMPONENTS, b);
            break;
        }
        case OP_DATE_EPOCH:
            // definitional axioms are attached to the argument
            break;
        default:
            UNREACHABLE();
        }
        return true;
    }

    void theory_date::apply_sort_cnstr(enode* n, sort* s) {
        SASSERT(u.is_date(s));
        ensure_var(n);
    }

    void theory_date::new_eq_eh(theory_var v1, theory_var v2) {
        expr* e1 = get_enode(v1)->get_expr();
        expr* e2 = get_enode(v2)->get_expr();
        if (u.is_date(e1) && u.is_date(e2))
            push_axiom(AX_MKINJ, e1);
    }

    void theory_date::new_diseq_eh(theory_var v1, theory_var v2) {
        expr* e1 = get_enode(v1)->get_expr();
        expr* e2 = get_enode(v2)->get_expr();
        if (u.is_date(e1) && u.is_date(e2))
            push_axiom(AX_INJ, e1, e2);
    }

    // ------------------------------------------------------------------
    // final check and model construction

    bool theory_date::epoch_value(enode* n, rational& val) {
        m_avalue.init(&ctx);
        for (enode* sib : *n->get_root()) {
            expr* e = sib->get_expr();
            if (!u.is_date(e))
                continue;
            app_ref ep(u.mk_epoch(e), m);
            if (ctx.e_internalized(ep) && m_avalue.get_value(ep, val) && val.is_int())
                return true;
        }
        return false;
    }

    final_check_status theory_date::final_check_eh(unsigned) {
        if (flush_axioms())
            return FC_CONTINUE;
        return final_check() ? FC_DONE : FC_CONTINUE;
    }

    /**
       \brief Detect distinct date classes whose epochs coincide in the
       current arithmetic assignment and force them to be merged or
       separated.
    */
    bool theory_date::final_check() {
        vector<std::pair<rational, enode*>> vals;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            enode* n = get_enode(v);
            if (!u.is_date(n->get_expr()) || !n->is_root())
                continue;
            rational val(0);
            epoch_value(n, val);
            vals.push_back(std::make_pair(val, n));
        }
        std::sort(vals.begin(), vals.end(),
                  [](auto const& p1, auto const& p2) { return p1.first < p2.first; });
        bool ok = true;
        for (unsigned i = 0; i + 1 < vals.size(); ++i) {
            if (vals[i].first == vals[i + 1].first) {
                assert_injectivity(vals[i].second->get_expr(), vals[i + 1].second->get_expr());
                ok = false;
            }
        }
        if (!ok)
            return false;
        return !propagate_components();
    }

    /**
       \brief Model-based propagation of the calendar bijection. When the
       epoch of a date term has an integer value in the current
       arithmetic assignment but its selector terms do not carry the
       components of that epoch day, assert the valid lemma
       epoch(t) = v => component(t) = civil-of-epoch(v). The
       days-from-civil axioms decide components -> epoch by plain
       bound propagation; this closes the inverse direction, which
       otherwise costs the integer solver a case split per date.
    */
    bool theory_date::propagate_components() {
        bool progress = false;
        m_avalue.init(&ctx);
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            expr* t = get_enode(v)->get_expr();
            if (!u.is_date(t))
                continue;
            app_ref ep(u.mk_epoch(t), m);
            if (!ctx.e_internalized(ep))
                continue;
            rational zv;
            if (!m_avalue.get_value(ep, zv) || !zv.is_int())
                continue;
            // one instantiation per (term, epoch value): the axioms are
            // complete without these lemmas (a final check can only be
            // accepted when the arithmetic model satisfies the
            // days-from-civil equations, which forces the components),
            // so skipping repeats cannot lose answers
            rational last;
            if (m_emitted.find(t, last) && last == zv)
                continue;
            rational tv[3];
            date_util::civil_of_epoch(zv, tv[0], tv[1], tv[2]);
            app_ref sels[3] = { app_ref(u.mk_year(t), m), app_ref(u.mk_month(t), m), app_ref(u.mk_day(t), m) };
            literal l_ep = null_literal;
            for (unsigned i = 0; i < 3; ++i) {
                if (!ctx.e_internalized(sels[i]))
                    continue;
                rational cv;
                if (m_avalue.get_value(sels[i], cv) && cv == tv[i])
                    continue;
                if (l_ep == null_literal) {
                    l_ep = mk_eq(ep, a.mk_int(zv), false);
                    ctx.mark_as_relevant(l_ep);
                }
                literal l_c = mk_eq(sels[i], a.mk_int(tv[i]), false);
                ctx.mark_as_relevant(l_c);
                ctx.mk_th_axiom(get_id(), ~l_ep, l_c);
                progress = true;
            }
            if (l_ep != null_literal)
                m_emitted.insert(t, zv);
        }
        return progress;
    }

    void theory_date::init_model(model_generator& mg) {
        m_factory = alloc(date_factory, m, get_family_id());
        mg.register_factory(m_factory);
    }

    model_value_proc* theory_date::mk_value(enode* n, model_generator& mg) {
        rational val(0);
        epoch_value(n, val);
        app* d = m_factory->mk_value(val, n->get_expr()->get_sort());
        return alloc(expr_wrapper_proc, d);
    }

    void theory_date::display(std::ostream& out) const {
        out << "theory date:\n";
        for (unsigned v = 0; v < get_num_vars(); ++v)
            out << v << ": " << enode_pp(get_enode(v), ctx) << "\n";
    }

}
