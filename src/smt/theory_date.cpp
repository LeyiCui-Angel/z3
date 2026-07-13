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
        m_e2s(m),
        m_cmp_atoms(m),
        m_dq1s(m),
        m_dq2s(m) {
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
            case AX_UNIT:
                assert_unit_axiom(m_e1s.get(i));
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

       In addition, assert the tautology
       (>= epoch(d) -B) or (<= epoch(d) B) with a large constant B, and
       prefer deciding both disjuncts true. The date constraints by
       themselves are translation-invariant, and on an unbounded lattice
       the integer solver's branch-and-bound over the calendar's div/mod
       structure drifts instead of converging. The preferred phases put
       every epoch inside a finite box (about +/- 11000 years), where
       branching and cuts terminate quickly; formulas that force a date
       outside the box simply flip the corresponding literal by conflict
       resolution, so neither soundness nor completeness is affected.
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
        rational B(4000000);
        if (char const* bs = getenv("DATE_BOX"))
            B = rational(atoi(bs));
        expr_ref lo(a.mk_ge(ep, a.mk_int(-B)), m);
        expr_ref hi(a.mk_le(ep, a.mk_int(B)), m);
        m_rw(lo);
        m_rw(hi);
        literal l_lo = mk_literal(lo);
        literal l_hi = mk_literal(hi);
        ctx.mark_as_relevant(l_lo);
        ctx.mark_as_relevant(l_hi);
        ctx.set_true_first_flag(l_lo.var());
        ctx.set_true_first_flag(l_hi.var());
        ctx.mk_th_axiom(get_id(), l_lo, l_hi);
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
        expr_ref_vector cuts(m);
        u.mk_civil_cuts(y, mo, cuts);
        for (expr* c : cuts)
            assert_unit_axiom(c);
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
        expr_ref_vector cuts(m);
        u.mk_civil_cuts(y, mo, cuts);
        for (expr* c : cuts)
            assert_unit_axiom(c);
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

    /**
       \brief Full eager encoding of a pure month shift term = shift(b)
       by 12*py + pm months: component axioms for term and base, the
       linear month-total link, the end-of-month clamp, and its cuts.
       Used directly for symbolic offsets, and as the escalation tier
       for constant shifts that resist window repair at final check.
    */
    void theory_date::push_shift_axioms(app* term, expr* b, expr* py, expr* pm) {
        push_axiom(AX_COMPONENTS, term);
        if (!u.is_mk(b))
            push_axiom(AX_COMPONENTS, b);
        expr_ref yb(u.mk_year(b), m), mb(u.mk_month(b), m), db(u.mk_day(b), m);
        expr_ref yt(u.mk_year(term), m), mt(u.mk_month(term), m);
        expr_ref shift(a.mk_add(a.mk_mul(a.mk_int(12), py), pm), m);
        push_axiom(AX_EQ, u.mk_month_total(yt, mt),
                   a.mk_add(u.mk_month_total(yb, mb), shift));
        push_axiom(AX_EQ, u.mk_day(term), u.mk_clamped_day(db, yt, mt));
        // clamp cuts: the clamped day never grows and shrinks by
        // at most 3 (day <= 31, month length >= 28)
        expr_ref dt(u.mk_day(term), m);
        push_axiom(AX_UNIT, a.mk_le(a.mk_sub(dt, db), a.mk_int(0)));
        push_axiom(AX_UNIT, a.mk_le(a.mk_sub(db, dt), a.mk_int(3)));
    }

    /**
       \brief Escalate a constant-shift term from the lazy tier to the
       full eager encoding. General shifts factor through the pure month
       shift; the mid term is created here and receives its own span
       cuts when it is internalized by the flushed axioms.
    */
    void theory_date::escalate_shift(expr* t) {
        app* ap = to_app(t);
        expr* b = ap->get_arg(0);
        rational py, pm, pd;
        if (!a.is_extended_numeral(ap->get_arg(1), py) ||
            !a.is_extended_numeral(ap->get_arg(2), pm) ||
            !a.is_extended_numeral(ap->get_arg(3), pd))
            return;
        if (u.is_sub(t)) {
            py.neg(); pm.neg(); pd.neg();
        }
        if ((rational(12) * py + pm).is_zero())
            return; // pure day shift, exact already
        expr_ref pye(a.mk_int(py), m), pme(a.mk_int(pm), m);
        IF_VERBOSE(4, verbose_stream() << "date escalate " << mk_pp(t, m) << "\n");
        // re-anchor the root base near the origin: the escalated
        // encoding's branch-and-bound behaves well at small magnitudes,
        // and by this point the model has typically drifted far away.
        // The clause is a tautology; both disjuncts are just preferred.
        expr* rb = t;
        while (is_app(rb) && (u.is_add(rb) || u.is_sub(rb)))
            rb = to_app(rb)->get_arg(0);
        expr_ref eprb(u.mk_epoch(rb), m);
        expr_ref lo(a.mk_ge(eprb, a.mk_int(-60000)), m);
        expr_ref hi(a.mk_le(eprb, a.mk_int(60000)), m);
        m_rw(lo);
        m_rw(hi);
        literal l_lo = mk_literal(lo);
        literal l_hi = mk_literal(hi);
        ctx.mark_as_relevant(l_lo);
        ctx.mark_as_relevant(l_hi);
        ctx.set_true_first_flag(l_lo.var());
        ctx.set_true_first_flag(l_hi.var());
        ctx.mk_th_lemma(get_id(), l_lo, l_hi);
        if (pd.is_zero())
            push_shift_axioms(ap, b, pye, pme);
        else {
            expr_ref zero(a.mk_int(0), m);
            expr* args[4] = { b, pye, pme, zero };
            app_ref mid(m.mk_app(get_family_id(), OP_DATE_ADD, 4, args), m);
            push_axiom(AX_EQ, u.mk_epoch(t), a.mk_add(u.mk_epoch(mid), a.mk_int(pd)));
            push_shift_axioms(mid, b, pye, pme);
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
        m_cmp_atoms.push_back(atom);
        ctx.push_trail(push_back_vector<expr_ref_vector>(m_cmp_atoms));
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
            rational ry, rm, rd;
            if (u.is_zero_month_shift(py, pm)) {
                // pure day shift: the base date is a valid date, so the
                // month step and the day clamp are the identity and the
                // epoch shifts exactly
                push_axiom(AX_EQ, u.mk_epoch(term), a.mk_add(u.mk_epoch(b), pd));
            }
            else if (a.is_extended_numeral(py, ry) && a.is_extended_numeral(pm, rm) &&
                     a.is_extended_numeral(pd, rd)) {
                // constant shift: assert only the epoch-span cuts here.
                // The month-shift function is enforced *lazily* at final
                // check: the model values are checked against exact
                // calendar arithmetic, mismatches are repaired by window
                // lemmas, and terms that resist repair are escalated to
                // the full component encoding (assert_shift_axioms).
                // Keeping the div/mod towers of that encoding out of the
                // eager constraints leaves the arithmetic solver a plain
                // difference-logic-like problem it can actually search.
                rational lo, hi;
                date_util::month_span_bounds(rational(12) * ry + rm, lo, hi);
                expr_ref ept(u.mk_epoch(term), m), epb(u.mk_epoch(b), m);
                push_axiom(AX_UNIT, a.mk_le(a.mk_sub(ept, epb), a.mk_int(hi + rd)));
                push_axiom(AX_UNIT, a.mk_le(a.mk_sub(epb, ept), a.mk_int(-(lo + rd))));
            }
            else if (u.is_zero(pd)) {
                // symbolic pure month shift: full eager encoding (rare)
                push_shift_axioms(term, b, py, pm);
            }
            else {
                // symbolic general shift: factor through the pure month
                // shift, then shift days exactly on epochs
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
            // selectors that occur in the input (internalized before the
            // search starts) pin their argument's calendar exactness;
            // selectors created by this solver's own lemmas do not
            if (!ctx.is_searching())
                m_sel_terms.insert(b);
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
        if (u.is_date(e1) && u.is_date(e2)) {
            push_axiom(AX_INJ, e1, e2);
            m_dq1s.push_back(e1);
            m_dq2s.push_back(e2);
            ctx.push_trail(push_back_vector<expr_ref_vector>(m_dq1s));
            ctx.push_trail(push_back_vector<expr_ref_vector>(m_dq2s));
        }
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
        return !propagate_windows();
    }

    /**
       \brief Compute the epoch that a date term must take once the free
       base dates are pinned to their current model values: exact
       calendar arithmetic over add/sub chains with numeral offsets,
       ground constructors by definition, everything else (free
       constants, symbolic offsets or constructors) by its current model
       value. Returns false when no value is available.
    */
    bool theory_date::implied_epoch(expr* t, obj_map<expr, rational>& memo, rational& z) {
        if (memo.find(t, z))
            return true;
        rational vy, vm, vd;
        bool computed = false;
        if (u.is_numeral_mk(t, vy, vm, vd)) {
            if (date_util::is_valid_civil(vy, vm, vd)) {
                z = date_util::days_from_civil(vy, vm, vd);
                computed = true;
            }
        }
        else if (u.is_add(t) || u.is_sub(t)) {
            app* ap = to_app(t);
            rational py, pm, pd, zb;
            if (a.is_extended_numeral(ap->get_arg(1), py) &&
                a.is_extended_numeral(ap->get_arg(2), pm) &&
                a.is_extended_numeral(ap->get_arg(3), pd) &&
                implied_epoch(ap->get_arg(0), memo, zb)) {
                if (u.is_sub(t)) {
                    py.neg(); pm.neg(); pd.neg();
                }
                z = date_util::add_to_epoch(zb, py, pm, pd);
                computed = true;
            }
        }
        if (!computed) {
            app_ref ep(u.mk_epoch(t), m);
            rational vv;
            if (!ctx.e_internalized(ep) || !m_avalue.get_value(ep, vv))
                return false;
            z = floor(vv);
        }
        memo.insert(t, z);
        return true;
    }

    /**
       \brief Model-based decision procedure for the calendar structure.

       The eager axioms (component axioms, month-total links, clamp and
       span cuts) are a complete reduction to linear integer arithmetic,
       but the resulting systems are translation-invariant and couple
       several div/mod towers, a shape on which the integer solver's
       branch-and-bound drifts instead of converging. This propagation
       constructs one *coordinated* candidate placement from the current
       model and asserts valid lemmas that make the placement (and every
       placement near it) propagate linearly:

       - value hints: for every free Date constant, the tautology
         (<= epoch(d) v) or (>= epoch(d) v) at its current model value v,
         both disjuncts with preferred phase true. Deciding both pins
         epoch(d) = v; an inconsistent pin is undone by conflict
         resolution. This anchors the otherwise floating bases.
       - chain window lemmas: for t = (date.add b py pm pd) with numeral
         offsets and month shift S = 12*py + pm != 0, the epoch of t is
         piecewise linear in the epoch of b across b's month window
         [s, s + len - 1] (target month start s', length len'):

             s <= epoch(b) <= s + min(len, len') - 1
                 => epoch(t) - epoch(b) = s' - s + pd
             s + len' <= epoch(b) <= s + len - 1       (if len > len')
                 => epoch(t) = s' + len' - 1 + pd      (end-of-month clamp)

       - component window lemmas: for a term whose selectors are in use,
         with epoch window [s, s + len - 1] of the month (Y, M):

             in-window => year(t) = Y, month(t) = M,
                          epoch(t) - day(t) = s - 1

       All windows are computed from the *implied* epochs (base pins
       propagated exactly through the chains in C++), so the emitted
       windows of one chain are aligned with each other by construction;
       windows read off the raw model values of each term individually
       disagree with the month-total links mid-search, and the resulting
       conflicts make the placement drift month by month.

       Every lemma is a valid fact of the theory, so this propagation
       can be damped or capped without affecting soundness; when it
       emits nothing, the eager axioms alone decide the final check.
    */
    /**
       \brief Evaluate the epoch of an add/sub chain exactly, given
       candidate epochs for the base dates. Fails on chains with
       non-numeral offsets.
    */
    bool theory_date::chain_eval(expr* t, obj_map<expr, rational> const& base, rational& z) {
        if (base.find(t, z))
            return true;
        rational vy, vm, vd;
        if (u.is_numeral_mk(t, vy, vm, vd)) {
            if (!date_util::is_valid_civil(vy, vm, vd))
                return false;
            z = date_util::days_from_civil(vy, vm, vd);
            return true;
        }
        if (u.is_add(t) || u.is_sub(t)) {
            app* ap = to_app(t);
            rational py, pm, pd, zb;
            if (!a.is_extended_numeral(ap->get_arg(1), py) ||
                !a.is_extended_numeral(ap->get_arg(2), pm) ||
                !a.is_extended_numeral(ap->get_arg(3), pd))
                return false;
            if (!chain_eval(ap->get_arg(0), base, zb))
                return false;
            if (u.is_sub(t)) {
                py.neg(); pm.neg(); pd.neg();
            }
            z = date_util::add_to_epoch(zb, py, pm, pd);
            return true;
        }
        return false;
    }

    /**
       \brief Search for a placement of the base dates that satisfies
       every currently assigned date atom (comparisons, equalities and
       disequalities between date terms), by iterative repair over exact
       C++ evaluation of the add/sub chains. The eager axioms decide the
       theory without this; a successful placement is used purely to
       coordinate the decision hints and window lemmas, replacing the
       integer solver's branch-and-bound drift with one consistent
       candidate that the SAT engine can adopt by propagation.
    */
    bool theory_date::find_placement(obj_map<expr, rational>& base) {
        // base dates: free constants and constructors with symbolic
        // arguments. Initialized from the last successful placement so
        // the suggested configuration stays stable across final checks;
        // new bases start from the current arithmetic model.
        ptr_vector<expr> bases;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            expr* t = get_enode(v)->get_expr();
            if (!u.is_date(t))
                continue;
            bool is_op = is_app(t) && to_app(t)->get_family_id() == get_family_id();
            rational vy, vm, vd;
            if (is_op && !(u.is_mk(t) && !u.is_numeral_mk(t, vy, vm, vd)))
                continue;
            if (base.contains(t))
                continue;
            rational z(0), vv;
            if (!(m_place_valid && m_place.find(t, z))) {
                app_ref ep(u.mk_epoch(t), m);
                if (ctx.e_internalized(ep) && m_avalue.get_value(ep, vv))
                    z = floor(vv);
            }
            base.insert(t, z);
            bases.push_back(t);
        }
        // constraints: (kind, lhs, rhs) with kind from the comparison
        // operators, plus equalities (E) and disequalities (D)
        struct cnstr { char k; expr* l; expr* r; };
        svector<cnstr> cs;
        for (expr* e : m_cmp_atoms) {
            app* atom = to_app(e);
            if (!ctx.b_internalized(atom) || !ctx.is_relevant(atom))
                continue;
            lbool tv = ctx.get_assignment(ctx.get_bool_var(atom));
            if (tv == l_undef)
                continue;
            char k;
            switch (atom->get_decl_kind()) {
            case OP_DATE_LT: k = tv == l_true ? '<' : 'g'; break; // g: >=
            case OP_DATE_LE: k = tv == l_true ? 'l' : '>'; break; // l: <=
            case OP_DATE_GT: k = tv == l_true ? '>' : 'l'; break;
            case OP_DATE_GE: k = tv == l_true ? 'g' : '<'; break;
            default: continue;
            }
            cs.push_back({ k, atom->get_arg(0), atom->get_arg(1) });
        }
        // equalities: all date terms merged into one class must coincide
        obj_map<enode, expr*> reps;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            expr* t = get_enode(v)->get_expr();
            if (!u.is_date(t))
                continue;
            enode* r = get_enode(v)->get_root();
            expr* rep = nullptr;
            if (reps.find(r, rep))
                cs.push_back({ 'E', rep, t });
            else
                reps.insert(r, t);
        }
        for (unsigned i = 0; i < m_dq1s.size(); ++i)
            cs.push_back({ 'D', m_dq1s.get(i), m_dq2s.get(i) });

        auto holds = [&](cnstr const& c, rational const& l, rational const& r) {
            switch (c.k) {
            case '<': return l < r;
            case 'l': return l <= r;
            case '>': return l > r;
            case 'g': return l >= r;
            case 'E': return l == r;
            case 'D': return l != r;
            default: return true;
            }
        };
        // the base date a chain's value follows
        auto root_base = [&](expr* t) -> expr* {
            while (is_app(t) && (u.is_add(t) || u.is_sub(t)))
                t = to_app(t)->get_arg(0);
            return base.contains(t) ? t : nullptr;
        };
        rational const big(100000000);
        unsigned n_violated = 0;
        for (unsigned iter = 0; iter < 400; ++iter) {
            unsigned first_violated = UINT_MAX;
            rational lv, rv;
            for (unsigned i = 0; i < cs.size(); ++i) {
                unsigned j = (i + iter) % cs.size();
                rational l, r;
                if (!chain_eval(cs[j].l, base, l) || !chain_eval(cs[j].r, base, r))
                    return false;
                if (!holds(cs[j], l, r)) {
                    first_violated = j;
                    lv = l;
                    rv = r;
                    break;
                }
            }
            if (first_violated == UINT_MAX) {
                m_place.reset();
                for (auto const& kv : base)
                    m_place.insert(kv.m_key, kv.m_value);
                m_place_valid = true;
                return true;
            }
            ++n_violated;
            cnstr const& c = cs[first_violated];
            // move one side's base towards satisfaction; alternate sides
            bool move_left = (n_violated % 2) == 0;
            expr* mb = move_left ? root_base(c.l) : root_base(c.r);
            if (!mb)
                mb = move_left ? root_base(c.r) : root_base(c.l);
            if (!mb)
                return false;
            rational target_delta;
            switch (c.k) {
            case '<': case 'l': target_delta = rv - lv - (c.k == '<' ? 1 : 0); break;
            case '>': case 'g': target_delta = rv - lv + (c.k == '>' ? 1 : 0); break;
            case 'E': target_delta = rv - lv; break;
            case 'D': target_delta = rational(1); break;
            default: target_delta = rational(0); break;
            }
            // first-order: chain values move about as fast as their base
            rational bump = (root_base(c.l) == mb) ? target_delta : -target_delta;
            if (bump.is_zero())
                bump = rational(1);
            rational nv = base[mb] + bump;
            if (nv > big) nv = big;
            if (nv < -big) nv = -big;
            base[mb] = nv;
            // refine: clamping plateaus make chains locally constant
            for (unsigned r2 = 0; r2 < 8; ++r2) {
                rational l, r;
                if (!chain_eval(c.l, base, l) || !chain_eval(c.r, base, r))
                    return false;
                if (holds(c, l, r))
                    break;
                rational d = (root_base(c.l) == mb) ? (r - l) : (l - r);
                if (d.is_zero())
                    d = rational(1);
                base[mb] = base[mb] + d;
            }
        }
        return false;
    }

    bool theory_date::propagate_windows() {
        m_avalue.init(&ctx);
        // the calendar exactness of a term only matters when the term
        // feeds a date atom the current assignment depends on: an
        // assigned relevant comparison, or an equality or disequality
        // between date terms. Everything else (e.g. terms under an
        // implication whose guard is false) places no constraint on the
        // model: the model evaluator computes date operations exactly
        // from the base constants' values, so internal epochs of unused
        // terms are free. Chasing them would drift forever. The gate
        // set is those atoms' operands closed under taking chain bases.
        obj_hashtable<expr> in_use;
        auto add_use = [&](expr* t0) {
            expr* t = t0;
            while (true) {
                if (in_use.contains(t))
                    return;
                in_use.insert(t);
                if (is_app(t) && (u.is_add(t) || u.is_sub(t)))
                    t = to_app(t)->get_arg(0);
                else
                    return;
            }
        };
        for (expr* e : m_cmp_atoms) {
            app* atom = to_app(e);
            if (!ctx.b_internalized(atom) || !ctx.is_relevant(atom))
                continue;
            if (ctx.get_assignment(ctx.get_bool_var(atom)) == l_undef)
                continue;
            add_use(atom->get_arg(0));
            add_use(atom->get_arg(1));
        }
        for (unsigned i = 0; i < m_dq1s.size(); ++i) {
            add_use(m_dq1s.get(i));
            add_use(m_dq2s.get(i));
        }
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            enode* n = get_enode(v);
            expr* t = n->get_expr();
            if (!u.is_date(t))
                continue;
            // date equalities: distinct terms merged into one class
            if (n->get_root() != n || n->get_class_size() > 1)
                add_use(t);
            // terms whose selectors occur in the input formula
            if (m_sel_terms.contains(t))
                add_use(t);
        }
        ptr_vector<expr> terms;
        bool stable = true;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            expr* t = get_enode(v)->get_expr();
            if (!u.is_date(t) || !in_use.contains(t))
                continue;
            terms.push_back(t);
            app_ref ep(u.mk_epoch(t), m);
            rational vv, last;
            if (ctx.e_internalized(ep) && m_avalue.get_value(ep, vv)) {
                if (!m_last_vals.find(t, last) || last != vv)
                    stable = false;
                m_last_vals.insert(t, vv);
            }
        }
        // exactness gate over the *model*: for every constant-shift
        // chain, the model value of its epoch must be the exact calendar
        // image of the model value of its base's epoch. Since these
        // terms carry only span cuts eagerly, this check is what makes
        // the final check sound; a final check is only accepted when it
        // passes and nothing else needs to be emitted.
        obj_map<expr, rational> exact;
        ptr_vector<expr> inexact;
        bool sel_mismatch = false;
        for (expr* t : terms) {
            rational z, vv, cv;
            // escalated terms are decided by their full eager encoding;
            // window lemmas for them would only interfere with it
            if (m_escalated.contains(t))
                continue;
            if (!implied_epoch(t, exact, z))
                continue;
            app_ref ep(u.mk_epoch(t), m);
            bool is_chain = (u.is_add(t) || u.is_sub(t));
            if (ctx.e_internalized(ep) && m_avalue.get_value(ep, vv) && vv != z) {
                IF_VERBOSE(4, verbose_stream() << "date gate " << mk_pp(t, m)
                           << " model=" << vv << " exact=" << z << "\n");
                if (is_chain) {
                    inexact.push_back(t);
                    if (!stable)
                        continue;
                    // healing: the window lemma for the term's current
                    // position may be dormant (its guards lost relevancy
                    // on backtracking) or garbage collected; drop the
                    // position from the emission history so the window
                    // is re-emitted (and re-marked relevant) in this
                    // round's emission pass
                    app_ref epb_(u.mk_epoch(to_app(t)->get_arg(0)), m);
                    rational vb_;
                    if (ctx.e_internalized(epb_) && m_avalue.get_value(epb_, vb_)) {
                        rational Yh, Mh, Dh;
                        date_util::civil_of_epoch(floor(vb_), Yh, Mh, Dh);
                        rational sh = date_util::days_from_civil(Yh, Mh, rational(1));
                        auto it = m_chain_emitted.find_iterator(t);
                        if (it != m_chain_emitted.end())
                            it->m_value.erase(sh);
                    }
                    // a term that marches month by month across a huge
                    // stretch of the timeline (deflected by some stale
                    // assignment), or that stays inexact for a very long
                    // stretch of settled positions, is escalated to the
                    // full eager encoding, which decides it independently
                    // of this propagation. Healthy window repairs stay
                    // local and intermittently exact, so they hit
                    // neither trigger.
                    unsigned cnt = 0;
                    m_stuck.find(t, cnt);
                    m_stuck.insert(t, cnt + 1);
                    rational lo_seen = vv, hi_seen = vv;
                    rational prev;
                    if (m_pos_lo.find(t, prev) && prev < lo_seen)
                        lo_seen = prev;
                    if (m_pos_hi.find(t, prev) && prev > hi_seen)
                        hi_seen = prev;
                    m_pos_lo.insert(t, lo_seen);
                    m_pos_hi.insert(t, hi_seen);
                    if ((hi_seen - lo_seen > rational(200000) || cnt + 1 >= 8192) &&
                        !m_escalated.contains(t)) {
                        m_escalated.insert(t);
                        escalate_shift(t);
                    }
                }
                                sel_mismatch = true;
                continue;
            }
            m_stuck.remove(t);
            rational Y, M, D;
            date_util::civil_of_epoch(z, Y, M, D);
            app_ref ys(u.mk_year(t), m), ms(u.mk_month(t), m), ds(u.mk_day(t), m);
            if ((ctx.e_internalized(ys) && m_avalue.get_value(ys, cv) && cv != Y) ||
                (ctx.e_internalized(ms) && m_avalue.get_value(ms, cv) && cv != M) ||
                (ctx.e_internalized(ds) && m_avalue.get_value(ds, cv) && cv != D))
                sel_mismatch = true;
        }
        if (inexact.empty() && !sel_mismatch)
            return false;
        // while the arithmetic assignment is still moving, just signal
        // that the final check cannot be accepted yet; acting on the
        // moving values would emit windows at meaningless positions
        if (!stable)
            return true;
        obj_map<expr, rational>& implied = exact;

        bool progress = false;
        // damper: true when (t, v) has not been emitted before; caps the
        // per-term history so an adversarial drift cannot grow it forever
        auto fresh = [&](obj_map<expr, vector<rational>>& seen, expr* t, rational const& v) {
            auto& vs = seen.insert_if_not_there(t, vector<rational>());
            if (vs.contains(v))
                return false;
            // bound the history but never block a new value permanently:
            // the lemmas are persistent, so re-emitting after a recycle
            // only costs duplicates
            if (vs.size() >= 128)
                vs.reset();
            vs.push_back(v);
            return true;
        };
        auto guard = [&](expr* atom) {
            expr_ref g(atom, m);
            m_rw(g);
            literal l = mk_literal(g);
            ctx.mark_as_relevant(l);
            ctx.set_true_first_flag(l.var());
            return l;
        };
        for (expr* t : terms) {
            rational z;
            if (m_escalated.contains(t))
                continue;
            if (!implied_epoch(t, implied, z))
                continue;
            app_ref ep(u.mk_epoch(t), m);
            if (!ctx.e_internalized(ep))
                continue;

        if (inexact.empty() && !sel_mismatch)
            return false;
        // while the arithmetic assignment is still moving, just signal
        // that the final check cannot be accepted yet; acting on the
        // moving values would emit windows at meaningless positions
        if (!stable)
            return true;
        obj_map<expr, rational>& implied = exact;
            // 2. component window lemmas for terms whose selectors
            // exist: for the suggested placement AND for the term's
            // current model position. The placement windows attract the
            // search to a known-good configuration; the model-position
            // windows make the exact semantics *locally enforced* right
            // where the model is, which is what repairs it. Emitting
            // only one of the two either chases a drifting model or
            // constrains a region the model has already left.
            app_ref ys(u.mk_year(t), m), ms(u.mk_month(t), m), ds(u.mk_day(t), m);
            bool have_sel = ctx.e_internalized(ys) || ctx.e_internalized(ms) || ctx.e_internalized(ds);
            rational zs[2] = { z, z };
            unsigned nz = 1;
            rational vv_t;
            if (m_avalue.get_value(ep, vv_t) && floor(vv_t) != z) {
                zs[1] = floor(vv_t);
                nz = 2;
            }
            for (unsigned zi = 0; zi < nz && have_sel; ++zi) {
                rational Y, M, D;
                date_util::civil_of_epoch(zs[zi], Y, M, D);
                rational s = date_util::days_from_civil(Y, M, rational(1));
                rational len = date_util::days_in_month(Y, M);
                if (!fresh(m_emitted, t, s))
                    continue;
                IF_VERBOSE(4, verbose_stream() << "date window " << mk_pp(t, m) << " " << Y << "-" << M << "\n");
                literal g1 = guard(a.mk_ge(ep, a.mk_int(s)));
                literal g2 = guard(a.mk_le(ep, a.mk_int(s + len - 1)));
                if (ctx.e_internalized(ys)) {
                    literal ly = mk_eq(ys, a.mk_int(Y), false);
                    ctx.mark_as_relevant(ly);
                    ctx.set_true_first_flag(ly.var());
                    ctx.mk_th_lemma(get_id(), ~g1, ~g2, ly);
                }
                if (ctx.e_internalized(ms)) {
                    literal lm = mk_eq(ms, a.mk_int(M), false);
                    ctx.mark_as_relevant(lm);
                    ctx.set_true_first_flag(lm.var());
                    ctx.mk_th_lemma(get_id(), ~g1, ~g2, lm);
                }
                if (ctx.e_internalized(ds)) {
                    literal ld = mk_eq(a.mk_sub(ep, ds), a.mk_int(s - 1), false);
                    ctx.mark_as_relevant(ld);
                    ctx.set_true_first_flag(ld.var());
                    ctx.mk_th_lemma(get_id(), ~g1, ~g2, ld);
                }
                progress = true;
            }

            // 3. chain window lemmas for month shifts with numeral offsets
            if (!u.is_add(t) && !u.is_sub(t))
                continue;
            app* ap = to_app(t);
            expr* b = ap->get_arg(0);
            rational py, pm, pd, zb;
            if (!a.is_extended_numeral(ap->get_arg(1), py) ||
                !a.is_extended_numeral(ap->get_arg(2), pm) ||
                !a.is_extended_numeral(ap->get_arg(3), pd))
                continue;
            if (u.is_sub(t)) {
                py.neg(); pm.neg(); pd.neg();
            }
            if ((rational(12) * py + pm).is_zero())
                continue; // pure day shift, exactly linear already
            app_ref epb(u.mk_epoch(b), m);
            if (!ctx.e_internalized(epb) || !implied_epoch(b, implied, zb))
                continue;
            rational zbs[2] = { zb, zb };
            unsigned nzb = 1;
            rational vv_b;
            if (m_avalue.get_value(epb, vv_b) && floor(vv_b) != zb) {
                zbs[1] = floor(vv_b);
                nzb = 2;
            }
            for (unsigned zi = 0; zi < nzb; ++zi) {
                rational Yb, Mb, Db;
                date_util::civil_of_epoch(zbs[zi], Yb, Mb, Db);
                rational sb = date_util::days_from_civil(Yb, Mb, rational(1));
                rational lenb = date_util::days_in_month(Yb, Mb);
                if (!fresh(m_chain_emitted, t, sb))
                    continue;
                unsigned wcount = 0;
                m_clears.find(t, wcount);
                m_clears.insert(t, wcount + 1);
                rational total = rational(12) * Yb + (Mb - rational(1)) + rational(12) * py + pm;
                rational Yp = div(total, rational(12));
                rational Mp = total - rational(12) * Yp + rational(1);
                rational sp = date_util::days_from_civil(Yp, Mp, rational(1));
                rational lenp = date_util::days_in_month(Yp, Mp);
                rational minlen = lenb < lenp ? lenb : lenp;
                IF_VERBOSE(4, verbose_stream() << "date chain window " << mk_pp(t, m)
                           << " " << Yb << "-" << Mb << " -> " << Yp << "-" << Mp << "\n");
                literal g1 = guard(a.mk_ge(epb, a.mk_int(sb)));
                literal g2 = guard(a.mk_le(epb, a.mk_int(sb + minlen - 1)));
                literal l1 = mk_eq(a.mk_sub(u.mk_epoch(t), epb), a.mk_int(sp - sb + pd), false);
                ctx.mark_as_relevant(l1);
                // prefer trying the consequence first; the stability
                // gating above keeps these equalities tied to settled
                // positions
                ctx.set_true_first_flag(l1.var());
                ctx.mk_th_lemma(get_id(), ~g1, ~g2, l1);
                if (lenb > lenp) {
                    literal h1 = guard(a.mk_ge(epb, a.mk_int(sb + lenp)));
                    literal h2 = guard(a.mk_le(epb, a.mk_int(sb + lenb - 1)));
                    literal l2 = mk_eq(u.mk_epoch(t), a.mk_int(sp + lenp - 1 + pd), false);
                    ctx.mark_as_relevant(l2);
                    ctx.set_true_first_flag(l2.var());
                    ctx.mk_th_lemma(get_id(), ~h1, ~h2, l2);
                }
                progress = true;
            }
        }
        if (progress)
            return true;
        if (inexact.empty())
            return false;
        // inexact chains with nothing left to emit: the window lemmas
        // are persistent (CLS_TH_LEMMA) but can still be garbage
        // collected; clear the resisting terms' emission histories so
        // their windows are re-emitted next round
        for (expr* t : inexact) {
            m_emitted.remove(t);
            m_chain_emitted.remove(t);
        }
        return true;
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
