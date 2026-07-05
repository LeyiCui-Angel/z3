/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.cpp

Abstract:

    Basic rewriting rules for the theory of calendar dates, together
    with the shared axiom builder used by both theory solvers.

Author:

    Claude 2026-07-05

--*/
#include "ast/rewriter/date_rewriter.h"

br_status date_rewriter::mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
    SASSERT(f->get_family_id() == get_fid());
    switch (f->get_decl_kind()) {
    case OP_DATE_MK:
        return BR_FAILED;
    case OP_DATE_YEAR:
    case OP_DATE_MONTH:
    case OP_DATE_DAY:
        SASSERT(num_args == 1);
        return mk_date_selector(f->get_decl_kind(), args[0], result);
    case OP_DATE_ADD:
        SASSERT(num_args == 4);
        return mk_date_add(args[0], args[1], args[2], args[3], result);
    case OP_DATE_SUB:
        SASSERT(num_args == 4);
        return mk_date_sub(args[0], args[1], args[2], args[3], result);
    case OP_DATE_LT:
    case OP_DATE_LE:
    case OP_DATE_GT:
    case OP_DATE_GE:
        SASSERT(num_args == 2);
        return mk_date_cmp(f->get_decl_kind(), args[0], args[1], result);
    default:
        return BR_FAILED;
    }
}

br_status date_rewriter::mk_date_add(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    rational ry, rm, rd, rpy, rpm, rpd;
    if (!m_arith.is_numeral(py, rpy) || !m_arith.is_numeral(pm, rpm) || !m_arith.is_numeral(pd, rpd))
        return BR_FAILED;
    // Adding the zero period is the identity on every (calendar-valid) date.
    if (rpy.is_zero() && rpm.is_zero() && rpd.is_zero()) {
        result = d;
        return BR_DONE;
    }
    if (!m_util.is_value(d, ry, rm, rd))
        return BR_FAILED;
    rational oy, om, od;
    date_decl_plugin::add(ry, rm, rd, rpy, rpm, rpd, oy, om, od);
    result = m_util.mk_date(oy, om, od);
    return BR_DONE;
}

br_status date_rewriter::mk_date_sub(expr* d, expr* py, expr* pm, expr* pd, expr_ref& result) {
    // date.sub(d, py, pm, pd) = date.add(d, -py, -pm, -pd)
    auto neg = [&](expr* e) -> expr* {
        rational r;
        if (m_arith.is_numeral(e, r))
            return m_arith.mk_int(-r);
        return m_arith.mk_uminus(e);
    };
    result = m_util.mk_add(d, neg(py), neg(pm), neg(pd));
    return BR_REWRITE2;
}

br_status date_rewriter::mk_date_selector(decl_kind k, expr* d, expr_ref& result) {
    rational ry, rm, rd;
    if (!m_util.is_value(d, ry, rm, rd))
        return BR_FAILED;
    switch (k) {
    case OP_DATE_YEAR:  result = m_arith.mk_int(ry); break;
    case OP_DATE_MONTH: result = m_arith.mk_int(rm); break;
    case OP_DATE_DAY:   result = m_arith.mk_int(rd); break;
    default: UNREACHABLE();
    }
    return BR_DONE;
}

br_status date_rewriter::mk_date_cmp(decl_kind k, expr* d1, expr* d2, expr_ref& result) {
    if (d1 == d2) {
        // Comparisons denote a total order on date values.
        result = m.mk_bool_val(k == OP_DATE_LE || k == OP_DATE_GE);
        return BR_DONE;
    }
    rational y1, m1, dd1, y2, m2, dd2;
    if (m_util.is_value(d1, y1, m1, dd1) && m_util.is_value(d2, y2, m2, dd2)) {
        bool lt = (y1 < y2) || (y1 == y2 && m1 < m2) || (y1 == y2 && m1 == m2 && dd1 < dd2);
        bool eq = y1 == y2 && m1 == m2 && dd1 == dd2;
        switch (k) {
        case OP_DATE_LT: result = m.mk_bool_val(lt); break;
        case OP_DATE_LE: result = m.mk_bool_val(lt || eq); break;
        case OP_DATE_GT: result = m.mk_bool_val(!lt && !eq); break;
        case OP_DATE_GE: result = m.mk_bool_val(!lt); break;
        default: UNREACHABLE();
        }
        return BR_DONE;
    }
    return BR_FAILED;
}

expr* date_axioms::mk_le_atom(expr* x, expr* y) {
    if (a.is_numeral(y))
        return a.mk_le(x, y);
    if (a.is_numeral(x))
        return a.mk_ge(y, x);
    return a.mk_le(a.mk_sub(x, y), mk_int(0));
}

expr* date_axioms::mk_lt_atom(expr* x, expr* y) {
    rational r;
    if (a.is_numeral(y, r))
        return a.mk_le(x, a.mk_int(r - 1));
    if (a.is_numeral(x, r))
        return a.mk_ge(y, a.mk_int(r + 1));
    return a.mk_le(a.mk_sub(x, y), mk_int(-1));
}

expr_ref date_axioms::mk_is_leap_year(expr* y) {
    expr* zero = mk_int(0);
    return expr_ref(m.mk_or(
        m.mk_and(m.mk_eq(a.mk_mod(y, mk_int(4)), zero),
                 m.mk_not(m.mk_eq(a.mk_mod(y, mk_int(100)), zero))),
        m.mk_eq(a.mk_mod(y, mk_int(400)), zero)), m);
}

expr_ref date_axioms::mk_days_in_month(expr* y, expr* mo) {
    expr_ref is30(m.mk_or(m.mk_eq(mo, mk_int(4)), m.mk_eq(mo, mk_int(6)),
                          m.mk_eq(mo, mk_int(9)), m.mk_eq(mo, mk_int(11))), m);
    expr_ref feb(m.mk_ite(mk_is_leap_year(y), mk_int(29), mk_int(28)), m);
    return expr_ref(m.mk_ite(is30, mk_int(30), m.mk_ite(m.mk_eq(mo, mk_int(2)), feb, mk_int(31))), m);
}

expr_ref date_axioms::mk_is_valid(expr* y, expr* mo, expr* d) {
    expr_ref_vector conjs(m);
    conjs.push_back(mk_le_atom(mk_int(1), mo));
    conjs.push_back(mk_le_atom(mo, mk_int(12)));
    conjs.push_back(mk_le_atom(mk_int(1), d));
    conjs.push_back(mk_le_atom(d, mk_days_in_month(y, mo)));
    return expr_ref(m.mk_and(conjs), m);
}

expr_ref date_axioms::mk_rata_die(expr* y, expr* mo, expr* d) {
    // days in the years before y
    expr_ref y1(a.mk_sub(y, mk_int(1)), m);
    expr_ref dby(a.mk_add(a.mk_mul(mk_int(365), y1),
                          a.mk_add(a.mk_idiv(y1, mk_int(4)),
                                   a.mk_sub(a.mk_idiv(y1, mk_int(400)), a.mk_idiv(y1, mk_int(100))))), m);
    // days in the months of y before mo
    static const int days_before[12] = { 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334 };
    expr_ref dbm(mk_int(days_before[11]), m);
    for (unsigned i = 11; i-- > 0; )
        dbm = m.mk_ite(m.mk_eq(mo, mk_int(i + 1)), mk_int(days_before[i]), dbm);
    expr_ref leap_adj(m.mk_ite(m.mk_and(mk_le_atom(mk_int(3), mo), mk_is_leap_year(y)),
                               mk_int(1), mk_int(0)), m);
    return expr_ref(a.mk_add(dby, a.mk_add(dbm, a.mk_add(leap_adj, d))), m);
}

expr_ref date_axioms::mk_rata_die(expr* d) {
    return mk_rata_die(dt.mk_year(d), dt.mk_month(d), dt.mk_day(d));
}

expr_ref date_axioms::mk_lex_lt(expr* d1, expr* d2, bool strict) {
    expr* y1 = dt.mk_year(d1),  * y2 = dt.mk_year(d2);
    expr* m1 = dt.mk_month(d1), * m2 = dt.mk_month(d2);
    expr* dd1 = dt.mk_day(d1),  * dd2 = dt.mk_day(d2);
    expr* last = strict ? mk_lt_atom(dd1, dd2) : mk_le_atom(dd1, dd2);
    return expr_ref(m.mk_or(mk_lt_atom(y1, y2),
                            m.mk_and(m.mk_eq(y1, y2), mk_lt_atom(m1, m2)),
                            m.mk_and(m.mk_eq(y1, y2), m.mk_eq(m1, m2), last)), m);
}

expr_ref date_axioms::valid_axiom(expr* t) {
    return mk_is_valid(dt.mk_year(t), dt.mk_month(t), dt.mk_day(t));
}

expr_ref date_axioms::recon_axiom(expr* t) {
    return expr_ref(m.mk_eq(t, dt.mk_date(dt.mk_year(t), dt.mk_month(t), dt.mk_day(t))), m);
}

expr_ref date_axioms::mk_axiom(app* c) {
    SASSERT(dt.is_mk(c));
    expr* y = c->get_arg(0), * mo = c->get_arg(1), * d = c->get_arg(2);
    expr_ref_vector eqs(m);
    eqs.push_back(m.mk_eq(dt.mk_year(c), y));
    eqs.push_back(m.mk_eq(dt.mk_month(c), mo));
    eqs.push_back(m.mk_eq(dt.mk_day(c), d));
    return expr_ref(m.mk_implies(mk_is_valid(y, mo, d), m.mk_and(eqs)), m);
}

expr_ref date_axioms::add_axiom(app* e) {
    SASSERT(dt.is_add(e) || dt.is_sub(e));
    expr* d = e->get_arg(0);
    expr* py = e->get_arg(1), * pm = e->get_arg(2), * pd = e->get_arg(3);
    if (dt.is_sub(e)) {
        auto neg = [&](expr* p) -> expr* {
            rational r;
            if (a.is_numeral(p, r))
                return a.mk_int(-r);
            return a.mk_uminus(p);
        };
        py = neg(py);
        pm = neg(pm);
        pd = neg(pd);
    }
    rational rpy, rpm, rpd;
    if (a.is_numeral(pd, rpd) && rpd.is_zero()) {
        // No day offset: the carry step is the identity, so the result is
        // the month-normalized, end-of-month-clamped triple itself. The
        // selector-level form propagates much better than the equation on
        // Rata Die day numbers, which the integer solver would have to
        // invert.
        expr_ref t(a.mk_sub(a.mk_add(dt.mk_month(d), a.mk_add(a.mk_mul(mk_int(12), py), pm)), mk_int(1)), m);
        expr_ref oy(a.mk_add(dt.mk_year(d), a.mk_idiv(t, mk_int(12))), m);
        expr_ref om(a.mk_add(a.mk_mod(t, mk_int(12)), mk_int(1)), m);
        expr_ref dim(mk_days_in_month(oy, om), m);
        expr_ref cd(m.mk_ite(mk_le_atom(dt.mk_day(d), dim), dt.mk_day(d), dim), m);
        return expr_ref(m.mk_and(m.mk_eq(dt.mk_year(e), oy),
                                 m.mk_eq(dt.mk_month(e), om),
                                 m.mk_eq(dt.mk_day(e), cd)), m);
    }
    if (a.is_numeral(py, rpy) && rpy.is_zero() && a.is_numeral(pm, rpm) && rpm.is_zero()) {
        // Pure day offset: month normalization and the end-of-month clamp
        // are the identity on (calendar-valid) dates, so the result is a
        // plain shift of the day number.
        return expr_ref(m.mk_eq(mk_rata_die(e), a.mk_add(mk_rata_die(d), pd)), m);
    }
    // Step 1 -- month normalization.
    expr_ref t(a.mk_sub(a.mk_add(dt.mk_month(d), a.mk_add(a.mk_mul(mk_int(12), py), pm)), mk_int(1)), m);
    expr_ref oy(a.mk_add(dt.mk_year(d), a.mk_idiv(t, mk_int(12))), m);
    expr_ref om(a.mk_add(a.mk_mod(t, mk_int(12)), mk_int(1)), m);
    // Step 2 -- end-of-month clamp.
    expr_ref dim(mk_days_in_month(oy, om), m);
    expr_ref cd(m.mk_ite(mk_le_atom(dt.mk_day(d), dim), dt.mk_day(d), dim), m);
    // Step 3 -- day carry: shift the day number by pd.
    expr_ref def(m.mk_eq(mk_rata_die(e), a.mk_add(mk_rata_die(oy, om, cd), pd)), m);
    // Redundant bounds linking the month offset M = 12*py + pm to the
    // Rata Die delta: each traversed month has 28..31 days and the
    // end-of-month clamp moves the day by at most -3. Implied by the
    // definition together with validity of d, but not derivable by
    // linear reasoning; without it a symbolic month offset leaves the
    // integer solver searching an unbounded range.
    expr_ref M(a.mk_add(a.mk_mul(mk_int(12), py), pm), m);
    expr_ref D(a.mk_sub(mk_rata_die(e), a.mk_add(mk_rata_die(d), pd)), m);
    expr_ref bounds(m.mk_and(
        m.mk_implies(mk_le_atom(mk_int(0), M),
                     m.mk_and(mk_le_atom(a.mk_sub(a.mk_mul(mk_int(28), M), mk_int(3)), D),
                              mk_le_atom(D, a.mk_mul(mk_int(31), M)))),
        m.mk_implies(mk_le_atom(M, mk_int(0)),
                     m.mk_and(mk_le_atom(a.mk_sub(a.mk_mul(mk_int(31), M), mk_int(3)), D),
                              mk_le_atom(D, a.mk_mul(mk_int(28), M))))), m);
    return expr_ref(m.mk_and(def, bounds), m);
}

expr_ref date_axioms::cmp_axiom(app* atom) {
    expr* d1 = atom->get_arg(0), * d2 = atom->get_arg(1);
    expr_ref def(m);
    if (dt.is_lt(atom))
        def = mk_lex_lt(d1, d2, true);
    else if (dt.is_le(atom))
        def = mk_lex_lt(d1, d2, false);
    else if (dt.is_gt(atom))
        def = mk_lex_lt(d2, d1, true);
    else if (dt.is_ge(atom))
        def = mk_lex_lt(d2, d1, false);
    else
        UNREACHABLE();
    return expr_ref(m.mk_eq(atom, def), m);
}

expr_ref date_axioms::bridge_axiom(expr* t, expr* u) {
    expr_ref rd_t = mk_rata_die(t), rd_u = mk_rata_die(u);
    return expr_ref(m.mk_and(
        m.mk_eq(m.mk_eq(t, u), m.mk_eq(rd_t, rd_u)),
        m.mk_eq(mk_lex_lt(t, u, true), mk_lt_atom(rd_t, rd_u))), m);
}
