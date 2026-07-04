/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_axioms.cpp

Abstract:

    Shared reduction of the native date theory to LIA + EUF.
    See date_axioms.h and Dates.smt2.

Author:

    Angel Cui 2026

--*/
#include "ast/date_axioms.h"

// maximum |offset| for which the day-carry loop is unfolded exactly;
// larger (or symbolic) offsets fall back to the serial-day encoding.
static const int64_t DAY_CARRY_CAP = 4000;

date_axiom_gen::date_axiom_gen(ast_manager& m):
    m(m), a(m), du(m) {
}

// Replace e by a fresh integer variable constrained to equal it, so that
// subsequent uses do not nest ITEs (which the rewriter would blow up when
// lifting equalities/div-mod over them).
void date_axiom_gen::bind(expr_ref& e) {
    expr_ref v(m.mk_fresh_const("date.v", a.mk_int()), m);
    push(m.mk_eq(v, e));
    e = v;
}

// ----- Euclidean div / mod elimination ---------------------------------

void date_axiom_gen::mk_divmod(expr* x, int n, expr_ref& q, expr_ref& r) {
    SASSERT(n > 0);
    q = expr_ref(m.mk_fresh_const("date.q", a.mk_int()), m);
    r = expr_ref(m.mk_fresh_const("date.r", a.mk_int()), m);
    push(m.mk_eq(x, a.mk_add(a.mk_mul(a.mk_int(n), q), r)));
    push(a.mk_le(a.mk_int(0), r));
    push(a.mk_lt(r, a.mk_int(n)));
}

expr_ref date_axiom_gen::mk_emod(expr* x, int n) {
    expr_ref q(m), r(m);
    mk_divmod(x, n, q, r);
    return r;
}

expr_ref date_axiom_gen::mk_ediv(expr* x, int n) {
    expr_ref q(m), r(m);
    mk_divmod(x, n, q, r);
    return q;
}

// ----- calendar helper expressions -------------------------------------

expr_ref date_axiom_gen::mk_is_leap(expr* y) {
    expr* c4   = m.mk_eq(mk_emod(y, 4),   a.mk_int(0));
    expr* c100 = m.mk_not(m.mk_eq(mk_emod(y, 100), a.mk_int(0)));
    expr* c400 = m.mk_eq(mk_emod(y, 400), a.mk_int(0));
    return expr_ref(m.mk_or(m.mk_and(c4, c100), c400), m);
}

expr_ref date_axiom_gen::mk_days_in_month(expr* y, expr* mo) {
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
// with 0 on one side: the arithmetic solvers only internalize atoms of the
// form (op term numeral); a term-vs-term atom is reported unsupported.
expr* date_axiom_gen::mk_le0(expr* x, expr* y) {   // x <= y
    return a.mk_le(a.mk_sub(x, y), a.mk_int(0));
}
expr* date_axiom_gen::mk_lt0(expr* x, expr* y) {   // x < y
    return a.mk_lt(a.mk_sub(x, y), a.mk_int(0));
}

expr_ref date_axiom_gen::mk_min(expr* x, expr* y) {
    expr_ref r(m.mk_ite(mk_le0(x, y), x, y), m);
    bind(r);
    return r;
}

expr_ref date_axiom_gen::mk_valid(expr* y, expr* mo, expr* d) {
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
expr_ref date_axiom_gen::mk_serial(expr* y, expr* mo, expr* d) {
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

expr_ref date_axiom_gen::mk_lex_lt(expr* y1, expr* m1, expr* d1,
                                   expr* y2, expr* m2, expr* d2) {
    expr* month_lt = m.mk_or(mk_lt0(m1, m2),
                             m.mk_and(m.mk_eq(m1, m2), mk_lt0(d1, d2)));
    expr* r = m.mk_or(mk_lt0(y1, y2),
                      m.mk_and(m.mk_eq(y1, y2), month_lt));
    return expr_ref(r, m);
}

// ----- date.add / date.sub encoding ------------------------------------

void date_axiom_gen::compute_norm(expr* d, expr* py, expr* pm,
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

void date_axiom_gen::day_carry(expr_ref& oy, expr_ref& om, expr_ref& tmp, int64_t k) {
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
expr* date_axiom_gen::neg_offset(expr* e, bool is_sub) {
    if (!is_sub)
        return e;
    rational v;
    if (a.is_numeral(e, v))
        return a.mk_int(-v);
    return a.mk_uminus(e);
}

void date_axiom_gen::emit_add_axioms(app* t, bool is_sub) {
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
        push(m.mk_and(eqs[0], eqs[1], eqs[2]));
    }
    else {
        // fallback: constrain the result via the serial-day equation.
        expr* lhs = mk_serial(Y, M, D);
        expr* rhs = a.mk_add(mk_serial(oy, om, clamp), pd);
        push(m.mk_eq(lhs, rhs));
    }
}

// ----- public entry points ---------------------------------------------

void date_axiom_gen::reduce_term(expr* t, expr_ref_vector& out) {
    SASSERT(du.is_date(t));
    m_out = &out;

    expr* Y = du.mk_year(t);
    expr* M = du.mk_month(t);
    expr* D = du.mk_day(t);

    // every Date value is calendar-valid
    push(mk_valid(Y, M, D));

    if (du.is_mk(t)) {
        // selector axioms, guaranteed only for calendar-valid triples
        app* ap = to_app(t);
        expr* y = ap->get_arg(0), *mo = ap->get_arg(1), *d = ap->get_arg(2);
        expr* conj = m.mk_and(m.mk_eq(Y, y), m.mk_eq(M, mo), m.mk_eq(D, d));
        push(m.mk_implies(mk_valid(y, mo, d), conj));
    }
    else {
        // reconstruction: ties t to its canonical constructor form, so
        // dates with equal projections are merged by congruence closure.
        push(m.mk_eq(t, du.mk_mk(Y, M, D)));
    }

    if (du.is_add(t))
        emit_add_axioms(to_app(t), false);
    else if (du.is_sub(t))
        emit_add_axioms(to_app(t), true);

    m_out = nullptr;
}

void date_axiom_gen::reduce_atom(app* atom, expr_ref_vector& out) {
    m_out = &out;
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
    }
    push(m.mk_eq(atom, body.get()));   // atom <=> body

    m_out = nullptr;
}
