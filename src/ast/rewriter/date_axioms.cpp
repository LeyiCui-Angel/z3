/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_axioms.cpp

Abstract:

    Axiomatization of the theory of calendar dates over linear integer
    arithmetic.

Author:

    Date theory extension 2026-07-05

--*/
#include "ast/rewriter/date_axioms.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"

void date_axioms::add_clause(expr* l1, expr* l2, expr* l3) {
    expr_ref_vector lits(m);
    lits.push_back(l1);
    if (l2) lits.push_back(l2);
    if (l3) lits.push_back(l3);
    m_add_clause(lits);
}

expr* date_axioms::mk_leap(expr* y) {
    return m.mk_or(
        m.mk_and(
            m.mk_eq(a.mk_mod(y, mk_int(4)), mk_int(0)),
            m.mk_not(m.mk_eq(a.mk_mod(y, mk_int(100)), mk_int(0)))),
        m.mk_eq(a.mk_mod(y, mk_int(400)), mk_int(0)));
}

expr* date_axioms::mk_clamp_day(expr* y, expr* mo, expr* d) {
    // min(d, days_in_month(y, mo)) for 1 <= d <= 31, case-split on the month
    // so that all arithmetic atoms compare a term against a numeral.
    auto mk_min = [&](int k) { return m.mk_ite(a.mk_le(d, mk_int(k)), d, mk_int(k)); };
    expr* is_short = m.mk_or(
        m.mk_eq(mo, mk_int(4)), m.mk_eq(mo, mk_int(6)),
        m.mk_eq(mo, mk_int(9)), m.mk_eq(mo, mk_int(11)));
    return m.mk_ite(
        m.mk_eq(mo, mk_int(2)),
        m.mk_ite(mk_leap(y), mk_min(29), mk_min(28)),
        m.mk_ite(is_short, mk_min(30), d));
}

expr* date_axioms::mk_valid(expr* y, expr* mo, expr* d) {
    // day <= days_in_month(y, mo), spelled out as a case split so that all
    // arithmetic atoms have the shape term <= numeral supported by the
    // arithmetic solvers (no ite terms inside atoms).
    expr_ref_vector long_months(m), short_months(m);
    for (int k : { 1, 3, 5, 7, 8, 10, 12 })
        long_months.push_back(m.mk_eq(mo, mk_int(k)));
    for (int k : { 4, 6, 9, 11 })
        short_months.push_back(m.mk_eq(mo, mk_int(k)));
    expr_ref leap(mk_leap(y), m);
    expr_ref_vector cases(m);
    cases.push_back(m.mk_and(mk_or(long_months), a.mk_le(d, mk_int(31))));
    cases.push_back(m.mk_and(mk_or(short_months), a.mk_le(d, mk_int(30))));
    cases.push_back(m.mk_and(m.mk_eq(mo, mk_int(2)), leap, a.mk_le(d, mk_int(29))));
    cases.push_back(m.mk_and(m.mk_eq(mo, mk_int(2)), m.mk_not(leap), a.mk_le(d, mk_int(28))));
    return m.mk_and(
        m.mk_and(a.mk_ge(mo, mk_int(1)), a.mk_le(mo, mk_int(12))),
        m.mk_and(a.mk_ge(d, mk_int(1)), mk_or(cases)));
}

expr* date_axioms::mk_days_from_civil(expr* y, expr* mo, expr* d) {
    // Howard Hinnant's days_from_civil; all divisions are by positive
    // numerals, so SMT-LIB div/mod coincide with floor division.
    expr* yp  = m.mk_ite(a.mk_le(mo, mk_int(2)), a.mk_sub(y, mk_int(1)), y);
    expr* era = a.mk_idiv(yp, mk_int(400));
    expr* yoe = a.mk_sub(yp, a.mk_mul(mk_int(400), era));
    expr* mp  = a.mk_mod(a.mk_add(mo, mk_int(9)), mk_int(12));
    expr* doy = a.mk_sub(
        a.mk_add(a.mk_idiv(a.mk_add(a.mk_mul(mk_int(153), mp), mk_int(2)), mk_int(5)), d),
        mk_int(1));
    expr* doe = a.mk_add(
        a.mk_mul(mk_int(365), yoe),
        a.mk_idiv(yoe, mk_int(4)),
        a.mk_sub(doy, a.mk_idiv(yoe, mk_int(100))));
    return a.mk_sub(a.mk_add(a.mk_mul(mk_int(146097), era), doe), mk_int(719468));
}

void date_axioms::date_term_axioms(expr* d) {
    // pin the selector terms: asserting a clause internalizes it, and the
    // resulting churn in the ast manager can collect unreferenced terms
    expr_ref y(u.mk_year(d), m);
    expr_ref mo(u.mk_month(d), m);
    expr_ref dd(u.mk_day(d), m);

    // validity: 1 <= month <= 12, 1 <= day <= days_in_month(year, month)
    add_clause(a.mk_ge(mo, mk_int(1)));
    add_clause(a.mk_le(mo, mk_int(12)));
    add_clause(a.mk_ge(dd, mk_int(1)));
    add_clause(a.mk_le(dd, mk_int(31)));
    for (int short_month : { 4, 6, 9, 11 })
        add_clause(m.mk_not(m.mk_eq(mo, mk_int(short_month))), a.mk_le(dd, mk_int(30)));
    add_clause(m.mk_not(m.mk_eq(mo, mk_int(2))), a.mk_le(dd, mk_int(29)));
    add_clause(m.mk_not(m.mk_eq(mo, mk_int(2))), mk_leap(y), a.mk_le(dd, mk_int(28)));

    // reconstruction: d = date.mk(date.year(d), date.month(d), date.day(d)).
    // Not instantiated for constructor terms: it would create an unbounded
    // chain of nested constructor terms, and for them it already follows
    // from the selector axioms together with congruence.
    if (!u.is_mk(d))
        add_clause(m.mk_eq(d, u.mk_mk(y, mo, dd)));
}

void date_axioms::mk_axioms(app* e) {
    SASSERT(u.is_mk(e));
    expr* y = e->get_arg(0);
    expr* mo = e->get_arg(1);
    expr* d = e->get_arg(2);
    // every date.mk occurrence carries the implicit validity obligation
    // on its arguments; under it the selector axioms are unconditional
    add_clause(mk_valid(y, mo, d));
    add_clause(m.mk_eq(u.mk_year(e), y));
    add_clause(m.mk_eq(u.mk_month(e), mo));
    add_clause(m.mk_eq(u.mk_day(e), d));
}

namespace {
    struct date_mk_collector {
        date_util&       u;
        ptr_vector<app>& mks;
        date_mk_collector(date_util& u, ptr_vector<app>& mks): u(u), mks(mks) {}
        void operator()(app* e) { if (u.is_mk(e) && e->is_ground()) mks.push_back(e); }
        void operator()(var* e) {}
        void operator()(quantifier* e) {}
    };
}

expr_ref date_axioms::conjoin_validity_obligations(ast_manager& m, expr* f) {
    expr_ref r(f, m);
    date_util u(m);
    ptr_vector<app> mks;
    date_mk_collector proc(u, mks);
    for_each_expr(proc, f);
    if (mks.empty())
        return r;
    date_axioms ax(m, [](expr_ref_vector const&) {});
    expr_ref_vector fmls(m);
    fmls.push_back(f);
    rational y, mo, d;
    for (app* e : mks) {
        if (u.is_date_numeral(e, y, mo, d)) {
            // concrete triples are decided directly
            if (!date_util::is_valid_date(y, mo, d))
                fmls.push_back(m.mk_false());
        }
        else
            fmls.push_back(ax.mk_valid(e->get_arg(0), e->get_arg(1), e->get_arg(2)));
    }
    if (fmls.size() > 1)
        r = m.mk_and(fmls);
    return r;
}

void date_axioms::add_axioms(app* e) {
    SASSERT(u.is_add(e) || u.is_sub(e));
    expr* d = e->get_arg(0);
    expr_ref py(e->get_arg(1), m), pm(e->get_arg(2), m), pd(e->get_arg(3), m);
    if (u.is_sub(e)) {
        py = a.mk_uminus(py);
        pm = a.mk_uminus(pm);
        pd = a.mk_uminus(pd);
    }
    expr* y0 = u.mk_year(d);
    expr* m0 = u.mk_month(d);
    expr* d0 = u.mk_day(d);

    // Step 1 -- month normalization
    expr* t  = a.mk_sub(a.mk_add(m0, a.mk_mul(mk_int(12), py), pm), mk_int(1));
    expr* oy = a.mk_add(y0, a.mk_idiv(t, mk_int(12)));
    expr* om = a.mk_add(a.mk_mod(t, mk_int(12)), mk_int(1));

    // Step 2 -- end-of-month clamp
    expr* clamp = mk_clamp_day(oy, om, d0);

    // Step 3 -- day carry, via the rata-die bijection: the result is the
    // unique calendar-valid date lying pd days after (oy, om, clamp).
    expr* n = a.mk_add(mk_days_from_civil(oy, om, clamp), pd);
    add_clause(m.mk_eq(mk_days_from_civil(u.mk_year(e), u.mk_month(e), u.mk_day(e)), n));
}

expr_ref date_axioms::mk_lex_lt(expr* d1, expr* d2, bool strict) {
    expr* y1 = u.mk_year(d1),  *y2 = u.mk_year(d2);
    expr* m1 = u.mk_month(d1), *m2 = u.mk_month(d2);
    expr* dd1 = u.mk_day(d1),  *dd2 = u.mk_day(d2);
    expr* last = strict ? a.mk_lt(dd1, dd2) : a.mk_le(dd1, dd2);
    return expr_ref(m.mk_or(
        a.mk_lt(y1, y2),
        m.mk_and(m.mk_eq(y1, y2), a.mk_lt(m1, m2)),
        m.mk_and(m.mk_eq(y1, y2), m.mk_eq(m1, m2), last)), m);
}

void date_axioms::cmp_axioms(app* e) {
    expr* d1 = e->get_arg(0);
    expr* d2 = e->get_arg(1);
    expr_ref def(m);
    if (u.is_lt(e))
        def = mk_lex_lt(d1, d2, true);
    else if (u.is_le(e))
        def = mk_lex_lt(d1, d2, false);
    else if (u.is_gt(e))
        def = mk_lex_lt(d2, d1, true);
    else if (u.is_ge(e))
        def = mk_lex_lt(d2, d1, false);
    else {
        UNREACHABLE();
        return;
    }
    add_clause(m.mk_not(e), def);
    add_clause(e, m.mk_not(def));
}
