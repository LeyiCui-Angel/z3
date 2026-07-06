/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_axioms.cpp

Abstract:

    Axiomatization of the Dates theory into linear integer arithmetic.

    The date arithmetic encoding follows the standard conversion between
    proleptic Gregorian dates and epoch days (days since 1970-01-01) due
    to Howard Hinnant. Both directions use only linear operations and
    divisions by positive integer constants, so all axioms stay within
    linear integer arithmetic. SMT-LIB div/mod by a positive constant
    agrees with floor division, which is what the conversion requires.

Author:

    Date theory extension 2026-07-04

--*/
#include "ast/rewriter/date_axioms.h"

namespace dates {

    axioms::axioms(ast_manager& m):
        m(m),
        dt(m),
        a(m) {
    }

    expr_ref axioms::mk_neg(expr* e) {
        rational r;
        if (a.is_numeral(e, r))
            return expr_ref(a.mk_int(-r), m);
        return expr_ref(a.mk_uminus(e), m);
    }

    expr_ref axioms::mk_is_leap(expr* y) {
        expr_ref mod4(a.mk_mod(y, mk_num(4)), m);
        expr_ref mod100(a.mk_mod(y, mk_num(100)), m);
        expr_ref mod400(a.mk_mod(y, mk_num(400)), m);
        expr_ref r(m.mk_or(m.mk_and(m.mk_eq(mod4, mk_num(0)),
                                    m.mk_not(m.mk_eq(mod100, mk_num(0)))),
                           m.mk_eq(mod400, mk_num(0))), m);
        return r;
    }

    expr_ref axioms::mk_days_in_month(expr* y, expr* mo) {
        expr_ref is30(m.mk_or(m.mk_eq(mo, mk_num(4)),
                              m.mk_eq(mo, mk_num(6)),
                              m.mk_eq(mo, mk_num(9)),
                              m.mk_eq(mo, mk_num(11))), m);
        expr_ref feb(m.mk_ite(mk_is_leap(y), mk_num(29), mk_num(28)), m);
        expr_ref r(m.mk_ite(m.mk_eq(mo, mk_num(2)), feb,
                            m.mk_ite(is30, mk_num(30), mk_num(31))), m);
        return r;
    }

    expr_ref axioms::mk_valid_triple(expr* y, expr* mo, expr* d) {
        ptr_buffer<expr> conjs;
        conjs.push_back(a.mk_le(mk_num(1), mo));
        conjs.push_back(a.mk_le(mo, mk_num(12)));
        conjs.push_back(a.mk_le(mk_num(1), d));
        conjs.push_back(a.mk_le(d, mk_days_in_month(y, mo)));
        expr_ref r(m.mk_and(conjs), m);
        return r;
    }

    expr_ref axioms::mk_days_from_civil(expr* y, expr* mo, expr* d) {
        // yadj = y - [mo <= 2]
        expr_ref yadj(m.mk_ite(a.mk_le(mo, mk_num(2)), a.mk_sub(y, mk_num(1)), y), m);
        // era = floor(yadj / 400), yoe = yadj - 400 * era in [0, 399]
        expr_ref era(a.mk_idiv(yadj, mk_num(400)), m);
        expr_ref yoe(a.mk_sub(yadj, a.mk_mul(mk_num(400), era)), m);
        // mp = (mo + 9) mod 12 in [0, 11]
        expr_ref mp(a.mk_mod(a.mk_add(mo, mk_num(9)), mk_num(12)), m);
        // doy = (153 * mp + 2) div 5 + d - 1 in [0, 365]
        expr_ref doy(a.mk_add(a.mk_idiv(a.mk_add(a.mk_mul(mk_num(153), mp), mk_num(2)), mk_num(5)),
                              a.mk_sub(d, mk_num(1))), m);
        // doe = 365 * yoe + yoe div 4 - yoe div 100 + doy in [0, 146096]
        expr_ref doe(a.mk_add(a.mk_mul(mk_num(365), yoe),
                              a.mk_sub(a.mk_idiv(yoe, mk_num(4)), a.mk_idiv(yoe, mk_num(100))),
                              doy), m);
        // epoch = 146097 * era + doe - 719468
        expr_ref r(a.mk_add(a.mk_mul(mk_num(146097), era), a.mk_sub(doe, mk_num(719468))), m);
        return r;
    }

    void axioms::mk_civil_from_days(expr* e, expr_ref& y, expr_ref& mo, expr_ref& d) {
        expr_ref z(a.mk_add(e, mk_num(719468)), m);
        // era = floor(z / 146097), doe = z - 146097 * era in [0, 146096]
        expr_ref era(a.mk_idiv(z, mk_num(146097)), m);
        expr_ref doe(a.mk_sub(z, a.mk_mul(mk_num(146097), era)), m);
        // yoe = (doe - doe div 1460 + doe div 36524 - doe div 146096) div 365 in [0, 399]
        expr_ref yoe_num(a.mk_add(a.mk_sub(doe, a.mk_idiv(doe, mk_num(1460))),
                                  a.mk_sub(a.mk_idiv(doe, mk_num(36524)),
                                           a.mk_idiv(doe, mk_num(146096)))), m);
        expr_ref yoe(a.mk_idiv(yoe_num, mk_num(365)), m);
        expr_ref y0(a.mk_add(yoe, a.mk_mul(mk_num(400), era)), m);
        // doy = doe - (365 * yoe + yoe div 4 - yoe div 100) in [0, 365]
        expr_ref doy(a.mk_sub(doe, a.mk_add(a.mk_mul(mk_num(365), yoe),
                                            a.mk_sub(a.mk_idiv(yoe, mk_num(4)),
                                                     a.mk_idiv(yoe, mk_num(100))))), m);
        // mp = (5 * doy + 2) div 153 in [0, 11]
        expr_ref mp(a.mk_idiv(a.mk_add(a.mk_mul(mk_num(5), doy), mk_num(2)), mk_num(153)), m);
        // d = doy - (153 * mp + 2) div 5 + 1 in [1, 31]
        d = a.mk_add(a.mk_sub(doy, a.mk_idiv(a.mk_add(a.mk_mul(mk_num(153), mp), mk_num(2)), mk_num(5))),
                     mk_num(1));
        // mo = mp + 3 if mp < 10 else mp - 9, in [1, 12]
        mo = m.mk_ite(a.mk_lt(mp, mk_num(10)), a.mk_add(mp, mk_num(3)), a.mk_sub(mp, mk_num(9)));
        // Jan and Feb belong to the following civil year
        y = m.mk_ite(a.mk_le(mo, mk_num(2)), a.mk_add(y0, mk_num(1)), y0);
    }

    expr_ref axioms::mk_epoch(expr* t) {
        expr_ref y(dt.mk_year(t), m), mo(dt.mk_month(t), m), d(dt.mk_day(t), m);
        return mk_days_from_civil(y, mo, d);
    }

    void axioms::validity_axiom(expr* t) {
        expr_ref y(dt.mk_year(t), m), mo(dt.mk_month(t), m), d(dt.mk_day(t), m);
        expr_ref valid = mk_valid_triple(y, mo, d);
        add_axiom(valid);
    }

    void axioms::reconstruction_axiom(expr* t) {
        expr_ref rebuilt(dt.mk_mk(dt.mk_year(t), dt.mk_month(t), dt.mk_day(t)), m);
        add_eq(t, rebuilt);
    }

    void axioms::constructor_axioms(app* t) {
        expr* y = t->get_arg(0);
        expr* mo = t->get_arg(1);
        expr* d = t->get_arg(2);
        // every date.mk occurrence carries the implicit validity
        // obligation of the DateSAT front-end on its argument triple
        // (Dates.smt2, :notes). Over concrete arguments the obligation
        // folds to true (calendar-valid triple) or false (invalid
        // application). With the triple valid, the selector equations
        // hold unconditionally.
        add_axiom(mk_valid_triple(y, mo, d));
        add_eq(dt.mk_year(t), y);
        add_eq(dt.mk_month(t), mo);
        add_eq(dt.mk_day(t), d);
    }

    void axioms::collect_obligations(expr* fml, expr_ref_vector& obligations) {
        ptr_vector<expr> todo;
        expr_fast_mark1 visited;
        todo.push_back(fml);
        while (!todo.empty()) {
            expr* e = todo.back();
            todo.pop_back();
            if (visited.is_marked(e) || !is_app(e))
                continue;
            visited.mark(e);
            app* t = to_app(e);
            for (expr* arg : *t)
                todo.push_back(arg);
            if (!dt.is_mk(t))
                continue;
            rational ry, rmo, rd;
            if (dt.is_numeral_mk(t, ry, rmo, rd)) {
                if (!date_util::is_valid_date(ry, rmo, rd))
                    obligations.push_back(m.mk_false());
            }
            else
                obligations.push_back(mk_valid_triple(t->get_arg(0), t->get_arg(1), t->get_arg(2)));
        }
    }

    void axioms::add_op_axioms(app* t, bool subtract) {
        expr* d = t->get_arg(0);
        expr_ref py(t->get_arg(1), m), pm(t->get_arg(2), m), pd(t->get_arg(3), m);
        if (subtract) {
            py = mk_neg(py);
            pm = mk_neg(pm);
            pd = mk_neg(pd);
        }
        expr_ref y(dt.mk_year(d), m), mo(dt.mk_month(d), m), dd(dt.mk_day(d), m);

        rational rpy, rpm, rpd;
        bool zero_months =
            a.is_numeral(py, rpy) && a.is_numeral(pm, rpm) &&
            (rational(12) * rpy + rpm).is_zero();

        expr_ref epoch(m);
        if (zero_months) {
            // fast path -- the net month offset is zero, so month
            // normalization is the identity and, since d denotes a valid
            // date, the end-of-month clamp keeps day(d). The epoch of the
            // result is the epoch of d shifted by pd; sharing d's epoch
            // term lets congruence closure cancel equal dates directly.
            epoch = a.mk_add(mk_epoch(d), pd);
            if (a.is_numeral(pd, rpd) && rpd.is_zero())
                add_eq(t, d);
        }
        else {
            // step 1 -- month normalization
            // t1 = month(d) + 12 * py + pm - 1
            expr_ref t1(a.mk_add(mo, a.mk_mul(mk_num(12), py), a.mk_sub(pm, mk_num(1))), m);
            expr_ref oy(a.mk_add(y, a.mk_idiv(t1, mk_num(12))), m);
            expr_ref om(a.mk_add(a.mk_mod(t1, mk_num(12)), mk_num(1)), m);

            // step 2 -- end-of-month clamp
            expr_ref dim = mk_days_in_month(oy, om);
            expr_ref clamp(m.mk_ite(a.mk_le(dd, dim), dd, dim), m);

            // step 3 -- day carry, via the epoch-day bijection
            epoch = a.mk_add(mk_days_from_civil(oy, om, clamp), pd);
        }

        expr_ref ry(m), rm(m), rd(m);
        mk_civil_from_days(epoch, ry, rm, rd);
        add_eq(dt.mk_year(t), ry);
        add_eq(dt.mk_month(t), rm);
        add_eq(dt.mk_day(t), rd);
        // redundant inverse direction; lets equal dates cancel without
        // re-deriving the epoch decomposition. Asserted through the
        // formula channel: it needs no anchoring, so it may be folded.
        add_axiom(m.mk_eq(mk_epoch(t), epoch));
    }

    void axioms::term_axioms(expr* t) {
        SASSERT(dt.is_date(t));
        validity_axiom(t);
        if (dt.is_mk(t))
            constructor_axioms(to_app(t));
        else
            reconstruction_axiom(t);
        if (dt.is_add(t))
            add_op_axioms(to_app(t), false);
        else if (dt.is_sub(t))
            add_op_axioms(to_app(t), true);
    }

    void axioms::compare_axioms(app* atom) {
        SASSERT(dt.is_comparison(atom));
        expr* d1 = atom->get_arg(0);
        expr* d2 = atom->get_arg(1);
        // date.gt and date.ge swap the arguments of date.lt and date.le
        if (dt.is_gt(atom) || dt.is_ge(atom))
            std::swap(d1, d2);
        bool strict = dt.is_lt(atom) || dt.is_gt(atom);

        expr_ref y1(dt.mk_year(d1), m), m1(dt.mk_month(d1), m), dd1(dt.mk_day(d1), m);
        expr_ref y2(dt.mk_year(d2), m), m2(dt.mk_month(d2), m), dd2(dt.mk_day(d2), m);

        expr_ref last(strict ? a.mk_lt(dd1, dd2) : a.mk_le(dd1, dd2), m);
        expr_ref lex(m.mk_or(a.mk_lt(y1, y2),
                             m.mk_and(m.mk_eq(y1, y2), a.mk_lt(m1, m2)),
                             m.mk_and(m.mk_eq(y1, y2), m.mk_eq(m1, m2), last)), m);
        add_iff(atom, lex);

        // equivalent formulation over epoch days; gives the solver the
        // chronological order directly when dates come from date.add/date.sub
        expr_ref e1 = mk_epoch(d1);
        expr_ref e2 = mk_epoch(d2);
        expr_ref by_epoch(strict ? a.mk_lt(e1, e2) : a.mk_le(e1, e2), m);
        add_iff(atom, by_epoch);
    }
}
