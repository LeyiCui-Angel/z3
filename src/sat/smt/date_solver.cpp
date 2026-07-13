/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_solver.cpp

Abstract:

    Theory solver for calendar dates (SAT/EUF core).

Author:

    Z3 date theory extension 2026-07-05

--*/
#include <algorithm>
#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_value.h"
#include "util/trail.h"

namespace dates {

    solver::solver(euf::solver& ctx, euf::theory_id id):
        th_euf_solver(ctx, ctx.get_manager().get_family_name(id), id),
        u(m),
        a(m),
        m_e1s(m),
        m_e2s(m),
        m_cmp_atoms(m),
        m_dq1s(m),
        m_dq2s(m) {
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        euf::theory_var v = th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, v);
        return v;
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        force_push();
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        auto lit = expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e) {
        force_push();
        visit_rec(m, e, false, false);
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());
    }

    bool solver::visit(expr* e) {
        if (visited(e))
            return true;
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        if (!n)
            n = mk_enode(e);
        if (n->is_attached_to(get_id()))
            return true;
        track_date(n);
        internalize_date_op(to_app(e));
        return true;
    }

    void solver::apply_sort_cnstr(euf::enode* n, sort* s) {
        SASSERT(u.is_date(s));
        force_push();
        track_date(n);
    }

    /**
       \brief Attach a theory variable; Date-sorted nodes are queued for an
       epoch-registration axiom (see assert_epoch_bound).
    */
    void solver::track_date(euf::enode* n) {
        if (is_attached_to_var(n))
            return;
        mk_var(n);
        if (u.is_date(n->get_expr()))
            push_axiom(AX_EPOCH_BOUND, n->get_expr());
    }

    // ------------------------------------------------------------------
    // deferred axiom queue.
    // axioms create and internalize new arithmetic terms; doing that from
    // within internalization re-enters the goal2sat conversion, which is
    // not re-entrant. Axioms are queued during internalization (and from
    // the eq/diseq callbacks) and flushed from unit_propagate().

    void solver::push_axiom(axiom_kind k, expr* e1, expr* e2) {
        m_kinds.push_back(k);
        m_e1s.push_back(e1);
        m_e2s.push_back(e2);
        ctx.push(push_back_vector<svector<axiom_kind>>(m_kinds));
        ctx.push(push_back_vector<expr_ref_vector>(m_e1s));
        ctx.push(push_back_vector<expr_ref_vector>(m_e2s));
    }

    bool solver::unit_propagate() {
        if (m_qhead == m_kinds.size())
            return false;
        force_push();
        ctx.push(value_trail<unsigned>(m_qhead));
        bool prop = false;
        for (; m_qhead < m_kinds.size() && !s().inconsistent(); ++m_qhead) {
            unsigned i = m_qhead;
            prop = true;
            switch (m_kinds[i]) {
            case AX_EQ:
                assert_axiom_eq(m_e1s.get(i), m_e2s.get(i));
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
                assert_mk_injectivity(expr2enode(m_e1s.get(i)));
                break;
            }
        }
        return prop;
    }

    void solver::assert_axiom_eq(expr* lhs, expr* rhs) {
        expr_ref _lhs(lhs, m), _rhs(rhs, m);
        rewrite(_rhs);
        if (_lhs == _rhs)
            return;
        add_unit(eq_internalize(_lhs, _rhs));
    }

    void solver::assert_unit_axiom(expr* e) {
        expr_ref c(e, m);
        rewrite(c);
        if (m.is_true(c))
            return;
        add_unit(mk_literal(c));
    }

    /**
       \brief atom <=> epoch order, for the queued comparison atom.
    */
    void solver::assert_cmp_axiom(app* t) {
        expr_ref ep1(u.mk_epoch(t->get_arg(0)), m);
        expr_ref ep2(u.mk_epoch(t->get_arg(1)), m);
        // build bound-form atoms (term <= numeral): this is the normal
        // form the arithmetic solvers expect for theory-created literals
        expr_ref ineq(m);
        switch (t->get_decl_kind()) {
        case OP_DATE_LT: ineq = a.mk_le(a.mk_sub(ep1, ep2), a.mk_int(-1)); break;
        case OP_DATE_LE: ineq = a.mk_le(a.mk_sub(ep1, ep2), a.mk_int(0)); break;
        case OP_DATE_GT: ineq = a.mk_le(a.mk_sub(ep2, ep1), a.mk_int(-1)); break;
        case OP_DATE_GE: ineq = a.mk_le(a.mk_sub(ep2, ep1), a.mk_int(0)); break;
        default: UNREACHABLE();
        }
        rewrite(ineq);
        sat::literal alit = expr2literal(t);
        if (m.is_true(ineq))
            add_unit(alit);
        else if (m.is_false(ineq))
            add_unit(~alit);
        else
            add_equiv(alit, mk_literal(ineq));
    }

    /**
       \brief Assert the tautology (<= epoch(d) 0) or (>= epoch(d) 0) so
       that epoch(d) is registered with the arithmetic solver and always
       has a value in the arithmetic model.
    */
    void solver::assert_epoch_bound(expr* d) {
        expr_ref ep(u.mk_epoch(d), m);
        expr_ref zero(a.mk_int(0), m);
        expr_ref le(a.mk_le(ep, zero), m);
        expr_ref ge(a.mk_ge(ep, zero), m);
        add_clause(mk_literal(le), mk_literal(ge));
        // soft box (a tautology whose disjuncts are preferred true):
        // the date constraints are translation-invariant, and preferring
        // epochs inside a finite box keeps the integer search from
        // drifting along the unbounded timeline. Formulas that force a
        // date outside the box flip the literal by conflict resolution.
        rational B(4000000);
        expr_ref lo(a.mk_ge(ep, a.mk_int(-B)), m);
        expr_ref hi(a.mk_le(ep, a.mk_int(B)), m);
        sat::literal l_lo = mk_literal(lo);
        sat::literal l_hi = mk_literal(hi);
        s().set_phase(l_lo);
        s().set_phase(l_hi);
        add_clause(l_lo, l_hi);
    }

    void solver::internalize_date_op(app* t) {
        switch (t->get_decl_kind()) {
        case OP_DATE_MK:
            push_axiom(AX_MK, t);
            break;
        case OP_DATE_ADD:
        case OP_DATE_SUB: {
            // date.sub is date.add with negated offsets
            bool is_sub = t->get_decl_kind() == OP_DATE_SUB;
            expr* b = t->get_arg(0);
            expr_ref py(t->get_arg(1), m), pm(t->get_arg(2), m), pd(t->get_arg(3), m);
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
                push_axiom(AX_EQ, u.mk_epoch(t), a.mk_add(u.mk_epoch(b), pd));
            }
            else if (a.is_extended_numeral(py, ry) && a.is_extended_numeral(pm, rm) &&
                     a.is_extended_numeral(pd, rd)) {
                // constant shift: assert only the epoch-span cuts here.
                // The month-shift function is enforced lazily at final
                // check (see propagate_windows); terms that resist
                // window repair are escalated to the full component
                // encoding. Keeping the div/mod towers of that encoding
                // out of the eager constraints leaves the arithmetic
                // solver a plain difference-logic-like problem.
                rational lo, hi;
                date_util::month_span_bounds(rational(12) * ry + rm, lo, hi);
                expr_ref ept(u.mk_epoch(t), m), epb(u.mk_epoch(b), m);
                push_axiom(AX_UNIT, a.mk_le(a.mk_sub(ept, epb), a.mk_int(hi + rd)));
                push_axiom(AX_UNIT, a.mk_le(a.mk_sub(epb, ept), a.mk_int(-(lo + rd))));
            }
            else if (u.is_zero(pd)) {
                // symbolic pure month shift: full eager encoding (rare)
                push_shift_axioms(t, b, py, pm);
            }
            else {
                // symbolic general shift: factor through the pure month
                // shift, then shift days exactly on epochs
                expr_ref zero(a.mk_int(0), m);
                expr* args[4] = { b, py, pm, zero };
                app_ref mid(m.mk_app(u.get_family_id(), OP_DATE_ADD, 4, args), m);
                push_axiom(AX_EQ, u.mk_epoch(t), a.mk_add(u.mk_epoch(mid), pd));
            }
            break;
        }
        case OP_DATE_YEAR:
        case OP_DATE_MONTH:
        case OP_DATE_DAY: {
            // the selector term itself is the component variable; for
            // date.mk arguments the constructor axioms already equate
            // the selectors with the arguments
            expr* b = t->get_arg(0);
            // selectors that occur in the input (internalized at base
            // level) pin their argument's calendar exactness; selectors
            // created by this solver's own lemmas do not
            if (s().at_base_lvl())
                m_sel_terms.insert(b);
            rational ry, rmo, rd;
            if (u.is_numeral_mk(b, ry, rmo, rd)) {
                // selectors of ground constructors are fixed (invalid
                // ground constructors force unsat through their own axioms)
                if (date_util::is_valid_civil(ry, rmo, rd)) {
                    rational v = t->get_decl_kind() == OP_DATE_YEAR ? ry :
                                 t->get_decl_kind() == OP_DATE_MONTH ? rmo : rd;
                    push_axiom(AX_EQ, t, a.mk_int(v));
                }
            }
            else if (!u.is_mk(b))
                push_axiom(AX_COMPONENTS, b);
            break;
        }
        case OP_DATE_LT:
        case OP_DATE_LE:
        case OP_DATE_GT:
        case OP_DATE_GE:
            push_axiom(AX_CMP, t);
            m_cmp_atoms.push_back(t);
            ctx.push(push_back_vector<expr_ref_vector>(m_cmp_atoms));
            break;
        case OP_DATE_EPOCH:
            // definitional axioms are attached to the argument
            break;
        default:
            UNREACHABLE();
        }
    }

    /**
       \brief Component axioms for a Date term: its selector terms form a
       valid civil triple whose days-from-civil image is its epoch. The
       selectors act as the component variables of the relational
       encoding; the inverse civil-of-epoch direction is never encoded,
       the integer solver searches over the bounded components instead.
    */
    void solver::assert_component_axioms(expr* d) {
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
        assert_axiom_eq(ep, u.mk_days_from_civil(y, mo, dd));
    }

    /**
       \brief Axioms for the strict constructor. The arguments must form a
       valid civil date: 1 <= m <= 12 and 1 <= d <= days-in-month(y, m);
       formulas that force date.mk onto out-of-range components are
       unsatisfiable. Under these constraints the epoch is defined by
       days-from-civil directly.
    */
    void solver::assert_mk_axioms(app* t) {
        expr* y = t->get_arg(0);
        expr* mo = t->get_arg(1);
        expr* d = t->get_arg(2);
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
        expr_ref ep(u.mk_epoch(t), m);
        assert_axiom_eq(ep, u.mk_days_from_civil(y, mo, d));
        // the components of the constructed date are the constructor
        // arguments. For ground constructors the definition above is
        // already a fixed epoch and the selector equalities are folded
        // by the rewriter wherever selectors occur.
        rational ry, rmo, rd;
        if (!u.is_numeral_mk(t, ry, rmo, rd)) {
            assert_axiom_eq(y, u.mk_year(t));
            assert_axiom_eq(mo, u.mk_month(t));
            assert_axiom_eq(d, u.mk_day(t));
        }
        // constructor-selector roundtrip fast-path
        if (u.is_year(y) && u.is_month(mo) && u.is_day(d)) {
            expr* x = to_app(y)->get_arg(0);
            if (x == to_app(mo)->get_arg(0) && x == to_app(d)->get_arg(0))
                assert_axiom_eq(ep, u.mk_epoch(x));
        }
    }

    /**
       \brief epoch(a) = epoch(b) => a = b
    */
    void solver::assert_injectivity(expr* d1, expr* d2) {
        expr_ref ep1(u.mk_epoch(d1), m);
        expr_ref ep2(u.mk_epoch(d2), m);
        sat::literal l_ep = eq_internalize(ep1, ep2);
        sat::literal l_d  = eq_internalize(d1, d2);
        add_clause(~l_ep, l_d);
    }

    void solver::new_diseq_eh(euf::th_eq const& eq) {
        euf::enode* n1 = var2enode(eq.v1());
        euf::enode* n2 = var2enode(eq.v2());
        if (u.is_date(n1->get_expr()) && u.is_date(n2->get_expr())) {
            push_axiom(AX_INJ, n1->get_expr(), n2->get_expr());
            m_dq1s.push_back(n1->get_expr());
            m_dq2s.push_back(n2->get_expr());
            ctx.push(push_back_vector<expr_ref_vector>(m_dq1s));
            ctx.push(push_back_vector<expr_ref_vector>(m_dq2s));
        }
    }

    /**
       \brief Components of dates are uniquely determined, so equal dates
       built by date.mk have equal constructor arguments. This gives the
       arithmetic solver the component equalities directly instead of
       requiring it to invert the days-from-civil map.
    */
    void solver::assert_mk_injectivity(euf::enode* n) {
        euf::enode* pivot = nullptr;
        for (euf::enode* sib : euf::enode_class(n->get_root())) {
            expr* s = sib->get_expr();
            if (!u.is_mk(s))
                continue;
            if (!pivot) {
                pivot = sib;
                continue;
            }
            expr* p = pivot->get_expr();
            sat::literal l_eq = eq_internalize(p, s);
            for (unsigned i = 0; i < 3; ++i)
                add_clause(~l_eq, eq_internalize(to_app(p)->get_arg(i), to_app(s)->get_arg(i)));
        }
    }

    /**
       \brief When two epoch terms merge (through congruence, unit axioms,
       or equalities proposed by the arithmetic solver's model-based theory
       combination), force the underlying dates to merge as well. When two
       date terms merge, propagate equalities between the arguments of
       date.mk terms in the merged class.
    */
    void solver::new_eq_eh(euf::th_eq const& eq) {
        euf::enode* n1 = var2enode(eq.v1());
        euf::enode* n2 = var2enode(eq.v2());
        expr* e1 = n1->get_expr();
        expr* e2 = n2->get_expr();
        if (u.is_date(e1) && u.is_date(e2)) {
            push_axiom(AX_MKINJ, e1);
            return;
        }
        if (!u.is_epoch(e1) || !u.is_epoch(e2))
            return;
        euf::enode* d1 = expr2enode(to_app(e1)->get_arg(0));
        euf::enode* d2 = expr2enode(to_app(e2)->get_arg(0));
        if (d1 && d2 && d1->get_root() != d2->get_root())
            push_axiom(AX_INJ, d1->get_expr(), d2->get_expr());
    }

    bool solver::epoch_value(euf::enode* n, rational& val) {
        arith::arith_value av(ctx);
        for (euf::enode* sib : euf::enode_class(n->get_root())) {
            expr* e = sib->get_expr();
            if (!u.is_date(e))
                continue;
            app_ref ep(u.mk_epoch(e), m);
            euf::enode* epn = expr2enode(ep);
            if (epn && av.get_value(ep, val) && val.is_int())
                return true;
        }
        return false;
    }

    /**
       \brief Full eager encoding of a pure month shift term = shift(b)
       by 12*py + pm months: component axioms for term and base, the
       linear month-total link, the end-of-month clamp, and its cuts.
       Used directly for symbolic offsets, and as the escalation tier
       for constant shifts that resist window repair at final check.
    */
    void solver::push_shift_axioms(app* term, expr* b, expr* py, expr* pm) {
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
       full eager encoding; see smt::theory_date::escalate_shift.
    */
    void solver::escalate_shift(expr* t) {
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
        IF_VERBOSE(4, verbose_stream() << "date euf escalate " << mk_pp(t, m) << "\n");
        // re-anchor the root base near the origin, where the escalated
        // encoding's search behaves well
        expr* rb = t;
        while (is_app(rb) && (u.is_add(rb) || u.is_sub(rb)))
            rb = to_app(rb)->get_arg(0);
        expr_ref eprb(u.mk_epoch(rb), m);
        sat::literal l_lo = mk_literal(a.mk_ge(eprb, a.mk_int(-60000)));
        sat::literal l_hi = mk_literal(a.mk_le(eprb, a.mk_int(60000)));
        s().set_phase(l_lo);
        s().set_phase(l_hi);
        add_clause(l_lo, l_hi);
        if (pd.is_zero())
            push_shift_axioms(ap, b, pye, pme);
        else {
            expr_ref zero(a.mk_int(0), m);
            expr* args[4] = { b, pye, pme, zero };
            app_ref mid(m.mk_app(u.get_family_id(), OP_DATE_ADD, 4, args), m);
            push_axiom(AX_EQ, u.mk_epoch(t), a.mk_add(u.mk_epoch(mid), a.mk_int(pd)));
            push_shift_axioms(mid, b, pye, pme);
        }
    }

    /**
       \brief The epoch a term must take given the model values of the
       base dates: exact calendar arithmetic over constant add/sub
       chains, ground constructors by definition, everything else by its
       current model value. See smt::theory_date::implied_epoch.
    */
    bool solver::implied_epoch(expr* t, obj_map<expr, rational>& memo, rational& z) {
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
            arith::arith_value av(ctx);
            rational vv;
            if (!expr2enode(ep) || !av.get_value(ep, vv))
                return false;
            z = floor(vv);
        }
        memo.insert(t, z);
        return true;
    }

    /**
       \brief Model-based decision procedure for constant add/sub chains,
       mirroring smt::theory_date::propagate_windows: an exactness gate
       over the model, month-window lemmas emitted at settled model
       positions, and a march detector that escalates resisting terms to
       the full eager encoding. All emitted clauses are valid lemmas.
    */
    bool solver::propagate_windows() {
        IF_VERBOSE(4, verbose_stream() << "date euf check\n");
        arith::arith_value av(ctx);
        // terms that feed a relevant assigned date atom, closed under
        // taking chain bases
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
            euf::enode* n = expr2enode(atom);
            if (!n)
                continue;
            sat::literal lit = expr2literal(atom);
            // every assigned comparison counts: the SAT/EUF core's model
            // validation requires the produced model to agree with the
            // assignment on all assigned atoms, relevant or not
            if (lit == sat::null_literal || s().value(lit) == l_undef)
                continue;
            add_use(atom->get_arg(0));
            add_use(atom->get_arg(1));
        }
        for (unsigned i = 0; i < m_dq1s.size(); ++i) {
            add_use(m_dq1s.get(i));
            add_use(m_dq2s.get(i));
        }
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            euf::enode* n = var2enode(v);
            expr* t = n->get_expr();
            if (!u.is_date(t))
                continue;
            if (n->get_root() != n || n->class_size() > 1)
                add_use(t);
            if (m_sel_terms.contains(t))
                add_use(t);
        }
        ptr_vector<expr> terms;
        obj_hashtable<expr> stable_term;
        for (unsigned v = 0; v < get_num_vars(); ++v) {
            expr* t = var2enode(v)->get_expr();
            if (!u.is_date(t) || !in_use.contains(t))
                continue;
            terms.push_back(t);
            app_ref ep(u.mk_epoch(t), m);
            rational vv, last;
            if (expr2enode(ep) && av.get_value(ep, vv)) {
                if (m_last_vals.find(t, last) && last == vv)
                    stable_term.insert(t);
                m_last_vals.insert(t, vv);
            }
        }
        auto stable_chain = [&](expr* t) {
            while (true) {
                if (!stable_term.contains(t))
                    return false;
                if (is_app(t) && (u.is_add(t) || u.is_sub(t)))
                    t = to_app(t)->get_arg(0);
                else
                    return true;
            }
        };
        // exactness gate over the model; see smt::theory_date
        obj_map<expr, rational> exact;
        ptr_vector<expr> inexact;
        ptr_vector<expr> exact_chains;
        ptr_vector<expr> to_escalate;
        bool sel_mismatch = false;
        for (expr* t : terms) {
            rational z, vv, cv;
            if (m_escalated.contains(t))
                continue;
            if (!implied_epoch(t, exact, z)) {
                IF_VERBOSE(4, verbose_stream() << "date euf noimplied " << mk_pp(t, m) << "\n");
                continue;
            }
            app_ref ep(u.mk_epoch(t), m);
            bool is_chain = (u.is_add(t) || u.is_sub(t));
            if (!expr2enode(ep) || !av.get_value(ep, vv)) {
                IF_VERBOSE(4, verbose_stream() << "date euf noval " << mk_pp(t, m) << "\n");
            }
            else if (vv != z) {
                IF_VERBOSE(4, verbose_stream() << "date euf gate " << mk_pp(t, m)
                           << " model=" << vv << " exact=" << z << "\n");
                if (is_chain) {
                    inexact.push_back(t);
                    if (!stable_chain(t))
                        continue;
                    // healing: re-emit the window of the current position
                    app_ref epb_(u.mk_epoch(to_app(t)->get_arg(0)), m);
                    rational vb_;
                    if (expr2enode(epb_) && av.get_value(epb_, vb_)) {
                        rational Yh, Mh, Dh;
                        date_util::civil_of_epoch(floor(vb_), Yh, Mh, Dh);
                        rational sh = date_util::days_from_civil(Yh, Mh, rational(1));
                        auto it = m_chain_emitted.find_iterator(t);
                        if (it != m_chain_emitted.end())
                            it->m_value.erase(sh);
                    }
                    // march detector; see smt::theory_date. Escalation
                    // is deferred: it creates literals, and the lp value
                    // queries used by this loop cannot run once new
                    // bounds are queued
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
                        to_escalate.push_back(t);
                    }
                }
                sel_mismatch = true;
                continue;
            }
            m_stuck.remove(t);
            if (is_chain)
                exact_chains.push_back(t);
            rational Y, M, D;
            date_util::civil_of_epoch(z, Y, M, D);
            app_ref ys(u.mk_year(t), m), ms(u.mk_month(t), m), ds(u.mk_day(t), m);
            if ((expr2enode(ys) && av.get_value(ys, cv) && cv != Y) ||
                (expr2enode(ms) && av.get_value(ms, cv) && cv != M) ||
                (expr2enode(ds) && av.get_value(ds, cv) && cv != D))
                sel_mismatch = true;
        }
        for (expr* t : to_escalate)
            escalate_shift(t);
        bool cover_missing = false;
        // coverage: exactness of the current assignment is not enough.
        // The arithmetic solver may still patch values when it builds
        // the final model, and columns merged only at the e-graph level
        // can be completed to different values, which silently breaks
        // the produced date values and the atoms over them. Accept only
        // when every in-use epoch is pinned at its accepted value by
        // assigned point bounds (a tautology pair whose disjuncts are
        // preferred true), and every exact chain's current window lemma
        // is active; emit the missing pins and windows otherwise.
        for (expr* t : terms) {
            rational zt;
            if (m_escalated.contains(t) || !exact.find(t, zt))
                continue;
            app_ref ept(u.mk_epoch(t), m);
            if (!expr2enode(ept))
                continue;
            sat::literal p1 = mk_literal(a.mk_ge(ept, a.mk_int(zt)));
            sat::literal p2 = mk_literal(a.mk_le(ept, a.mk_int(zt)));
            if (s().value(p1) == l_true && s().value(p2) == l_true)
                continue;
            auto& vs = m_cover_emitted.insert_if_not_there(t, vector<rational>());
            if (vs.contains(zt)) {
                // pin proposed before and not adopted; accept as is
                // rather than looping (falls back to the plain reads)
                continue;
            }
            if (vs.size() >= 128)
                vs.reset();
            vs.push_back(zt);
            s().set_phase(p1);
            s().set_phase(p2);
            add_clause(p1, p2);
            cover_missing = true;
        }
        for (expr* t : exact_chains) {
            expr* b = to_app(t)->get_arg(0);
            rational zb;
            if (!exact.find(b, zb))
                continue;
            rational Yb, Mb, Db;
            date_util::civil_of_epoch(zb, Yb, Mb, Db);
            rational sb = date_util::days_from_civil(Yb, Mb, rational(1));
            app_ref epb(u.mk_epoch(b), m);
            sat::literal g1 = mk_literal(a.mk_ge(epb, a.mk_int(sb)));
            rational lenb = date_util::days_in_month(Yb, Mb);
            rational lenp;
            {
                rational py, pm, pd;
                app* ap = to_app(t);
                if (!a.is_extended_numeral(ap->get_arg(1), py) ||
                    !a.is_extended_numeral(ap->get_arg(2), pm) ||
                    !a.is_extended_numeral(ap->get_arg(3), pd))
                    continue;
                if (u.is_sub(t)) {
                    py.neg(); pm.neg();
                }
                rational total = rational(12) * Yb + (Mb - rational(1)) + rational(12) * py + pm;
                rational Yp = div(total, rational(12));
                rational Mp = total - rational(12) * Yp + rational(1);
                lenp = date_util::days_in_month(Yp, Mp);
            }
            rational minlen = lenb < lenp ? lenb : lenp;
            sat::literal g2 = mk_literal(a.mk_le(epb, a.mk_int(sb + minlen - 1)));
            bool active = s().value(g1) == l_true && s().value(g2) == l_true;
            if (!active && lenb > lenp) {
                // clamp piece: requires its own guards
                sat::literal h1 = mk_literal(a.mk_ge(epb, a.mk_int(sb + lenp)));
                sat::literal h2 = mk_literal(a.mk_le(epb, a.mk_int(sb + lenb - 1)));
                active = s().value(h1) == l_true && s().value(h2) == l_true;
            }
            IF_VERBOSE(4, verbose_stream() << "date euf cover " << mk_pp(t, m)
                       << " base=" << zb << " win=" << sb << " g1=" << s().value(g1)
                       << " g2=" << s().value(g2) << " active=" << active << "\n");
            if (!active) {
                auto it = m_chain_emitted.find_iterator(t);
                if (it != m_chain_emitted.end())
                    it->m_value.erase(sb);
                cover_missing = true;
                continue;
            }
        }
        if (inexact.empty() && !sel_mismatch && !cover_missing) {
            IF_VERBOSE(4, verbose_stream() << "date euf accept\n");
            return false;
        }
        obj_map<expr, rational>& implied = exact;

        bool progress = false;
        auto fresh = [&](obj_map<expr, vector<rational>>& seen, expr* t, rational const& v) {
            auto& vs = seen.insert_if_not_there(t, vector<rational>());
            if (vs.contains(v))
                return false;
            if (vs.size() >= 128)
                vs.reset();
            vs.push_back(v);
            return true;
        };
        auto guard = [&](expr* atom) {
            expr_ref g(atom, m);
            sat::literal l = mk_literal(g);
            s().set_phase(l);
            return l;
        };
        for (expr* t : terms) {
            rational z;
            if (m_escalated.contains(t))
                continue;
            if (!stable_chain(t))
                continue;
            if (!implied_epoch(t, implied, z))
                continue;
            app_ref ep(u.mk_epoch(t), m);
            if (!expr2enode(ep))
                continue;

            // component window lemmas for terms whose selectors exist,
            // at the implied position and at the model position
            app_ref ys(u.mk_year(t), m), ms(u.mk_month(t), m), ds(u.mk_day(t), m);
            bool have_sel = expr2enode(ys) || expr2enode(ms) || expr2enode(ds);
            rational zs[2] = { z, z };
            unsigned nz = 1;
            rational vv_t;
            // read the model position from the snapshot taken before any
            // clause was added: the lp solver cannot answer value queries
            // once new bounds are queued
            if (m_last_vals.find(t, vv_t) && floor(vv_t) != z) {
                zs[1] = floor(vv_t);
                nz = 2;
            }
            for (unsigned zi = 0; zi < nz && have_sel; ++zi) {
                rational Y, M, D;
                date_util::civil_of_epoch(zs[zi], Y, M, D);
                rational sw = date_util::days_from_civil(Y, M, rational(1));
                rational len = date_util::days_in_month(Y, M);
                if (!fresh(m_emitted, t, sw))
                    continue;
                IF_VERBOSE(4, verbose_stream() << "date euf window " << mk_pp(t, m) << " " << Y << "-" << M << "\n");
                sat::literal g1 = guard(a.mk_ge(ep, a.mk_int(sw)));
                sat::literal g2 = guard(a.mk_le(ep, a.mk_int(sw + len - 1)));
                if (expr2enode(ys)) {
                    sat::literal ly = eq_internalize(ys, a.mk_int(Y));
                    s().set_phase(ly);
                    add_clause(~g1, ~g2, ly);
                }
                if (expr2enode(ms)) {
                    sat::literal lm = eq_internalize(ms, a.mk_int(M));
                    s().set_phase(lm);
                    add_clause(~g1, ~g2, lm);
                }
                if (expr2enode(ds)) {
                    sat::literal ld = eq_internalize(a.mk_sub(ep, ds), a.mk_int(sw - 1));
                    s().set_phase(ld);
                    add_clause(~g1, ~g2, ld);
                }
                progress = true;
            }

            // chain window lemmas for constant month shifts
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
            if (!expr2enode(epb) || !implied_epoch(b, implied, zb))
                continue;
            rational zbs[2] = { zb, zb };
            unsigned nzb = 1;
            rational vv_b;
            if (m_last_vals.find(b, vv_b) && floor(vv_b) != zb) {
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
                rational total = rational(12) * Yb + (Mb - rational(1)) + rational(12) * py + pm;
                rational Yp = div(total, rational(12));
                rational Mp = total - rational(12) * Yp + rational(1);
                rational sp = date_util::days_from_civil(Yp, Mp, rational(1));
                rational lenp = date_util::days_in_month(Yp, Mp);
                rational minlen = lenb < lenp ? lenb : lenp;
                IF_VERBOSE(4, verbose_stream() << "date euf chain window " << mk_pp(t, m)
                           << " " << Yb << "-" << Mb << " -> " << Yp << "-" << Mp << "\n");
                sat::literal g1 = guard(a.mk_ge(epb, a.mk_int(sb)));
                sat::literal g2 = guard(a.mk_le(epb, a.mk_int(sb + minlen - 1)));
                sat::literal l1 = eq_internalize(a.mk_sub(u.mk_epoch(t), epb), a.mk_int(sp - sb + pd));
                s().set_phase(l1);
                add_clause(~g1, ~g2, l1);
                if (lenb > lenp) {
                    sat::literal h1 = guard(a.mk_ge(epb, a.mk_int(sb + lenp)));
                    sat::literal h2 = guard(a.mk_le(epb, a.mk_int(sb + lenb - 1)));
                    sat::literal l2 = eq_internalize(u.mk_epoch(t), a.mk_int(sp + lenp - 1 + pd));
                    s().set_phase(l2);
                    add_clause(~h1, ~h2, l2);
                }
                progress = true;
            }
        }
        if (progress)
            return true;
        if (inexact.empty() && !cover_missing)
            return false;
        // nothing left to emit: clear the resisting terms' histories so
        // their windows are re-emitted next round
        for (expr* t : inexact) {
            m_emitted.remove(t);
            m_chain_emitted.remove(t);
        }
        return true;
    }

    sat::check_result solver::check() {
        // flush any remaining queued axioms before accepting the model.
        // injectivity is enforced through new_eq_eh: epoch terms are shared
        // with the arithmetic solver, whose model-based theory combination
        // proposes equalities between equal-valued epochs.
        if (m_qhead < m_kinds.size())
            return sat::check_result::CR_CONTINUE;
        if (propagate_windows())
            return sat::check_result::CR_CONTINUE;
        return sat::check_result::CR_DONE;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(u.is_date(n->get_expr()));
        // constant add/sub chains are computed from the model value of
        // their base date with exact calendar arithmetic, so the date
        // values in the model are calendar-consistent by construction
        // regardless of how the arithmetic model was completed
        rational val(0);
        bool found = false;
        for (euf::enode* sib : euf::enode_class(n->get_root())) {
            expr* e = sib->get_expr();
            if (!u.is_date(e) || (!u.is_add(e) && !u.is_sub(e)))
                continue;
            app* ap = to_app(e);
            rational py, pm, pd, zb;
            if (!a.is_extended_numeral(ap->get_arg(1), py) ||
                !a.is_extended_numeral(ap->get_arg(2), pm) ||
                !a.is_extended_numeral(ap->get_arg(3), pd))
                continue;
            euf::enode* bn = expr2enode(ap->get_arg(0));
            expr* bv;
            if (!bn || !(bv = values.get(bn->get_root_id(), nullptr)) || !u.is_date_value(bv, zb))
                continue;
            if (u.is_sub(e)) {
                py.neg(); pm.neg(); pd.neg();
            }
            val = date_util::add_to_epoch(zb, py, pm, pd);
            found = true;
            break;
        }
        // otherwise read the epoch from the model being constructed (the
        // epoch node is a declared dependency): the arithmetic solver may
        // complete its model with values that differ from the current
        // assignment, and the date value must match the completed model
        if (!found) {
            // prefer the root's own epoch term, then any sibling's
            euf::enode* root = n->get_root();
            for (unsigned pass = 0; pass < 2 && !found; ++pass) {
                for (euf::enode* sib : euf::enode_class(root)) {
                    expr* e = sib->get_expr();
                    if (!u.is_date(e))
                        continue;
                    if (pass == 0 && sib != root)
                        continue;
                    app_ref ep(u.mk_epoch(e), m);
                    euf::enode* epn = expr2enode(ep);
                    expr* v;
                    if (epn && (v = values.get(epn->get_root_id(), nullptr)) && a.is_numeral(v, val)) {
                        found = true;
                        break;
                    }
                }
            }
        }
        if (!found)
            epoch_value(n, val);
        values.set(n->get_root_id(), u.mk_date_value(val));
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (!u.is_date(n->get_expr())) {
            dep.insert(n, nullptr);
            return true;
        }
        // date values are read off their epoch terms and, for add/sub
        // chains, computed from the base date's value; depend on both
        bool has_dep = false;
        for (euf::enode* sib : euf::enode_class(n->get_root())) {
            expr* e = sib->get_expr();
            if (!u.is_date(e))
                continue;
            app_ref ep(u.mk_epoch(e), m);
            euf::enode* epn = expr2enode(ep);
            if (epn) {
                dep.add(n, epn->get_root());
                has_dep = true;
            }
            if (u.is_add(e) || u.is_sub(e)) {
                euf::enode* bn = expr2enode(to_app(e)->get_arg(0));
                if (bn && bn->get_root() != n->get_root()) {
                    dep.add(n, bn->get_root());
                    has_dep = true;
                }
            }
        }
        if (!has_dep)
            dep.insert(n, nullptr);
        return true;
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx, get_id());
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "theory date:\n";
        for (unsigned v = 0; v < get_num_vars(); ++v)
            out << v << ": " << mk_pp(var2enode(v)->get_expr(), m) << "\n";
        return out;
    }

}
