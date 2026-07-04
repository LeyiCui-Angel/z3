/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_date.cpp

Abstract:

    Legacy-SMT theory solver for the native theory of calendar dates.
    See theory_date.h and Dates.smt2 for the specification.

    The solver reduces the date theory to integer arithmetic.  For every
    Date term t it introduces the three integer projections
    date.year(t), date.month(t), date.day(t) and asserts:

      * validity:   1 <= month(t) <= 12  and
                    1 <= day(t) <= days_in_month(year(t), month(t));
      * reconstruction: t = date.mk(year(t), month(t), day(t))
                    (so two dates with equal projections are congruent);
      * for date.mk(y,m,d): the selector axioms, guarded by validity of
                    (y,m,d);
      * for date.add / date.sub: the three-step calendar algorithm from
                    Dates.smt2, encoded over the projections.

    Comparisons are reduced to the lexicographic order on the projections.

Author:

    Angel Cui 2026

--*/

#include "smt/theory_date.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "ast/ast_pp.h"

namespace smt {

    // maximum |offset| for which the day-carry loop is unfolded exactly;
    // larger (or symbolic) offsets fall back to the serial-day encoding.
    static const int64_t DAY_CARRY_CAP = 4000;

    theory_date::theory_date(context& ctx):
        theory(ctx, ctx.get_manager().mk_family_id("date")),
        du(ctx.get_manager()),
        a(ctx.get_manager()),
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

    // Assert a reduction axiom through the ordinary assertion path.  During
    // the initial (base-level) internalization of the user assertions, the
    // context's internalize_assertions() loop picks up these newly asserted
    // formulas and preprocesses them via reduce_assertions() -- exactly the
    // normalization the arithmetic solver needs.  Injecting them raw with
    // mk_th_axiom instead makes theory_arith / theory_lra report spurious
    // incompleteness on satisfiable instances.
    void theory_date::assert_axiom(expr* fml) {
        // Only buffer here.  Rewriting/internalizing now would run while the
        // caller still holds raw, unreferenced intermediate terms.
        m_axioms.push_back(fml);
    }

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

    // ----- Euclidean div / mod elimination ---------------------------------

    void theory_date::mk_divmod(expr* x, int n, expr_ref& q, expr_ref& r) {
        SASSERT(n > 0);
        q = expr_ref(m.mk_fresh_const("date.q", a.mk_int()), m);
        r = expr_ref(m.mk_fresh_const("date.r", a.mk_int()), m);
        assert_axiom(m.mk_eq(x, a.mk_add(a.mk_mul(a.mk_int(n), q), r)));
        assert_axiom(a.mk_le(a.mk_int(0), r));
        assert_axiom(a.mk_lt(r, a.mk_int(n)));
    }

    expr_ref theory_date::mk_emod(expr* x, int n) {
        expr_ref q(m), r(m);
        mk_divmod(x, n, q, r);
        return r;
    }

    expr_ref theory_date::mk_ediv(expr* x, int n) {
        expr_ref q(m), r(m);
        mk_divmod(x, n, q, r);
        return q;
    }

    // ----- calendar helper expressions -------------------------------------

    expr_ref theory_date::mk_is_leap(expr* y) {
        expr* c4   = m.mk_eq(mk_emod(y, 4),   a.mk_int(0));
        expr* c100 = m.mk_not(m.mk_eq(mk_emod(y, 100), a.mk_int(0)));
        expr* c400 = m.mk_eq(mk_emod(y, 400), a.mk_int(0));
        return expr_ref(m.mk_or(m.mk_and(c4, c100), c400), m);
    }

    expr_ref theory_date::mk_days_in_month(expr* y, expr* mo) {
        expr_ref leap = mk_is_leap(y);
        expr* feb = m.mk_ite(leap, a.mk_int(29), a.mk_int(28));
        expr* in30[4] = { m.mk_eq(mo, a.mk_int(4)),  m.mk_eq(mo, a.mk_int(6)),
                          m.mk_eq(mo, a.mk_int(9)),  m.mk_eq(mo, a.mk_int(11)) };
        expr* is30 = m.mk_or(4, in30);
        expr_ref r(m.mk_ite(m.mk_eq(mo, a.mk_int(2)), feb,
                            m.mk_ite(is30, a.mk_int(30), a.mk_int(31))), m);
        bind(r);   // cap the ITE behind a fresh variable
        return r;
    }

    // Comparisons with a term (not a numeral) on both sides must be written
    // with 0 on one side: theory_lra only internalizes atoms of the form
    // (op term numeral); a term-vs-term atom is reported unsupported.
    expr* theory_date::mk_le0(expr* x, expr* y) {   // x <= y
        return a.mk_le(a.mk_sub(x, y), a.mk_int(0));
    }
    expr* theory_date::mk_lt0(expr* x, expr* y) {   // x < y
        return a.mk_lt(a.mk_sub(x, y), a.mk_int(0));
    }

    expr_ref theory_date::mk_min(expr* x, expr* y) {
        expr_ref r(m.mk_ite(mk_le0(x, y), x, y), m);
        bind(r);
        return r;
    }

    expr_ref theory_date::mk_valid(expr* y, expr* mo, expr* d) {
        expr* cs[4] = {
            a.mk_le(a.mk_int(1), mo),
            a.mk_le(mo, a.mk_int(12)),
            a.mk_le(a.mk_int(1), d),
            mk_le0(d, mk_days_in_month(y, mo))
        };
        return expr_ref(m.mk_and(std::span<expr* const>(cs, 4)), m);
    }

    // Rata-die style serial day number (proleptic Gregorian), a bijection
    // between valid dates and the integers.  Used only for the fallback
    // encoding of date.add with large / symbolic day offsets.
    expr_ref theory_date::mk_serial(expr* y, expr* mo, expr* d) {
        expr* shift = m.mk_ite(a.mk_le(mo, a.mk_int(2)), a.mk_int(1), a.mk_int(0));
        expr* y2  = a.mk_sub(y, shift);
        expr_ref era = mk_ediv(y2, 400);
        expr* yoe = a.mk_sub(y2, a.mk_mul(a.mk_int(400), era));
        expr_ref mp = mk_emod(a.mk_add(mo, a.mk_int(9)), 12);
        expr* doy = a.mk_add(mk_ediv(a.mk_add(a.mk_mul(a.mk_int(153), mp), a.mk_int(2)), 5),
                             a.mk_sub(d, a.mk_int(1)));
        expr* doe = a.mk_add(a.mk_mul(a.mk_int(365), yoe),
                             mk_ediv(yoe, 4));
        doe = a.mk_sub(doe, mk_ediv(yoe, 100));
        doe = a.mk_add(doe, doy);
        expr* r = a.mk_sub(a.mk_add(a.mk_mul(era, a.mk_int(146097)), doe), a.mk_int(719468));
        return expr_ref(r, m);
    }

    expr_ref theory_date::mk_lex_lt(expr* y1, expr* m1, expr* d1,
                                    expr* y2, expr* m2, expr* d2) {
        expr* month_lt = m.mk_or(mk_lt0(m1, m2),
                                 m.mk_and(m.mk_eq(m1, m2), mk_lt0(d1, d2)));
        expr* r = m.mk_or(mk_lt0(y1, y2),
                          m.mk_and(m.mk_eq(y1, y2), month_lt));
        return expr_ref(r, m);
    }

    // ----- date.add / date.sub encoding ------------------------------------

    void theory_date::compute_norm(expr* d, expr* py, expr* pm,
                                   expr_ref& oy, expr_ref& om, expr_ref& clamp) {
        expr* Y = du.mk_year(d);
        expr* M = du.mk_month(d);
        expr* D = du.mk_day(d);
        // raw_month = month(d) + 12*py + pm ; t = raw_month - 1
        expr* raw = a.mk_add(M, a.mk_mul(a.mk_int(12), py), pm);
        expr* t = a.mk_sub(raw, a.mk_int(1));
        expr_ref q(m), r(m);
        mk_divmod(t, 12, q, r);
        oy = expr_ref(a.mk_add(Y, q), m);
        om = expr_ref(a.mk_add(r, a.mk_int(1)), m);
        clamp = mk_min(D, mk_days_in_month(oy, om));
    }

    // Replace e by a fresh integer variable constrained to equal it, so that
    // subsequent uses do not nest ITEs (which the rewriter would blow up when
    // lifting equalities/div-mod over them).
    void theory_date::bind(expr_ref& e) {
        expr_ref v(m.mk_fresh_const("date.v", a.mk_int()), m);
        assert_axiom(m.mk_eq(v, e));
        e = v;
    }

    void theory_date::day_carry(expr_ref& oy, expr_ref& om, expr_ref& tmp, int64_t k) {
        if (k == 0)
            return;
        bool forward = k > 0;
        int64_t ak = forward ? k : -k;
        int64_t iters = ak / 28 + 3;
        for (int64_t it = 0; it < iters; ++it) {
            // flatten the running values to fresh variables each round
            bind(oy); bind(om); bind(tmp);
            if (forward) {
                expr* cur_dim = mk_days_in_month(oy, om);
                expr* fire = mk_lt0(cur_dim, tmp);   // tmp > cur_dim
                expr* is_dec = m.mk_eq(om, a.mk_int(12));
                expr* om_adv = m.mk_ite(is_dec, a.mk_int(1), a.mk_add(om, a.mk_int(1)));
                expr* oy_adv = m.mk_ite(is_dec, a.mk_add(oy, a.mk_int(1)), oy.get());
                expr* tmp_adv = a.mk_sub(tmp, cur_dim);
                oy  = m.mk_ite(fire, oy_adv, oy.get());
                om  = m.mk_ite(fire, om_adv, om.get());
                tmp = m.mk_ite(fire, tmp_adv, tmp.get());
            }
            else {
                expr* fire = a.mk_lt(tmp, a.mk_int(1));
                expr* is_jan = m.mk_eq(om, a.mk_int(1));
                expr* om_ret = m.mk_ite(is_jan, a.mk_int(12), a.mk_sub(om, a.mk_int(1)));
                expr* oy_ret = m.mk_ite(is_jan, a.mk_sub(oy, a.mk_int(1)), oy.get());
                expr* new_dim = mk_days_in_month(oy_ret, om_ret);
                expr* tmp_ret = a.mk_add(tmp, new_dim);
                oy  = m.mk_ite(fire, oy_ret, oy.get());
                om  = m.mk_ite(fire, om_ret, om.get());
                tmp = m.mk_ite(fire, tmp_ret, tmp.get());
            }
        }
    }

    // -e when is_sub, keeping a numeral literal a numeral (so date.sub's
    // negated day offset is still recognized by the concrete unfolding).
    expr* theory_date::neg_offset(expr* e, bool is_sub) {
        if (!is_sub)
            return e;
        rational v;
        if (a.is_numeral(e, v))
            return a.mk_int(-v);
        return a.mk_uminus(e);
    }

    void theory_date::emit_add_axioms(app* t, bool is_sub) {
        // date.sub(d, py, pm, pd) = date.add(d, -py, -pm, -pd).
        expr* d  = t->get_arg(0);
        expr_ref py(neg_offset(t->get_arg(1), is_sub), m);
        expr_ref pm(neg_offset(t->get_arg(2), is_sub), m);
        expr_ref pd(neg_offset(t->get_arg(3), is_sub), m);
        expr_ref oy(m), om(m), clamp(m);
        compute_norm(d, py, pm, oy, om, clamp);

        expr* Y = du.mk_year(t);
        expr* M = du.mk_month(t);
        expr* D = du.mk_day(t);

        rational k;
        bool is_num = a.is_numeral(pd, k);
        if (is_num && k.is_int64() && k.get_int64() >= -DAY_CARRY_CAP && k.get_int64() <= DAY_CARRY_CAP) {
            // exact unfolding of the day-carry loop
            expr_ref tmp(a.mk_add(clamp, pd), m);
            day_carry(oy, om, tmp, k.get_int64());
            expr* eqs[3] = { m.mk_eq(Y, oy), m.mk_eq(M, om), m.mk_eq(D, tmp) };
            assert_axiom(m.mk_and(eqs[0], eqs[1], eqs[2]));
        }
        else {
            // fallback: constrain the result via the serial-day equation.
            // result denotes the calendar-valid date that is pd days after
            // the clamped (oy, om, clamp) date.
            expr* lhs = mk_serial(Y, M, D);
            expr* rhs = a.mk_add(mk_serial(oy, om, clamp), pd);
            assert_axiom(m.mk_eq(lhs, rhs));
        }
    }

    // ----- generic per-Date-term axioms ------------------------------------

    void theory_date::emit_date_axioms(expr* t) {
        if (!du.is_date(t) || m_processed.contains(t))
            return;
        m_processed.insert(t);

        expr* Y = du.mk_year(t);
        expr* M = du.mk_month(t);
        expr* D = du.mk_day(t);

        // every Date value is calendar-valid
        assert_axiom(mk_valid(Y, M, D));

        if (du.is_mk(t)) {
            // selector axioms, guaranteed only for calendar-valid triples
            app* ap = to_app(t);
            expr* y = ap->get_arg(0), *mo = ap->get_arg(1), *d = ap->get_arg(2);
            expr* conj = m.mk_and(m.mk_eq(Y, y), m.mk_eq(M, mo), m.mk_eq(D, d));
            assert_axiom(m.mk_implies(mk_valid(y, mo, d), conj));
        }
        else {
            // reconstruction: ties t to its canonical constructor form, so
            // dates with equal projections are merged by congruence closure.
            assert_axiom(m.mk_eq(t, du.mk_mk(Y, M, D)));
        }

        if (du.is_add(t))
            emit_add_axioms(to_app(t), false);
        else if (du.is_sub(t))
            emit_add_axioms(to_app(t), true);
    }

    // ----- internalization -------------------------------------------------

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

    void theory_date::internalize_predicate(app* atom) {
        if (m_processed.contains(atom))
            return;
        m_processed.insert(atom);
        expr* x = atom->get_arg(0);
        expr* y = atom->get_arg(1);
        expr* yx = du.mk_year(x), *mx = du.mk_month(x), *dx = du.mk_day(x);
        expr* yy = du.mk_year(y), *my = du.mk_month(y), *dy = du.mk_day(y);

        expr_ref body(m);
        if (du.is_lt(atom))
            body = mk_lex_lt(yx, mx, dx, yy, my, dy);
        else if (du.is_gt(atom))
            body = mk_lex_lt(yy, my, dy, yx, mx, dx);
        else if (du.is_le(atom))
            body = expr_ref(m.mk_not(mk_lex_lt(yy, my, dy, yx, mx, dx)), m); // !(y < x)
        else if (du.is_ge(atom))
            body = expr_ref(m.mk_not(mk_lex_lt(yx, mx, dx, yy, my, dy)), m); // !(x < y)
        else {
            UNREACHABLE();
            return;
        }
        // atom <=> body
        assert_axiom(m.mk_eq(atom, body.get()));
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
