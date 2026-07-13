/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declaration plugin for the theory of calendar dates.

Author:

    Z3 date theory extension 2026-07-05

--*/
#include <algorithm>
#include <climits>
#include "ast/date_decl_plugin.h"
#include "ast/ast_pp.h"

date_decl_plugin::~date_decl_plugin() {
    if (m_manager)
        m_manager->dec_ref(m_date);
}

void date_decl_plugin::set_manager(ast_manager* m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_date = m->mk_sort(symbol("Date"), sort_info(m_family_id, DATE_SORT));
    m->inc_ref(m_date);
}

sort* date_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) {
    if (k != DATE_SORT || num_parameters != 0) {
        m_manager->raise_exception("unexpected date sort");
        return nullptr;
    }
    return m_date;
}

func_decl* date_decl_plugin::mk_decl(decl_kind k, char const* name, unsigned arity,
                                     sort* const* domain, sort* range) {
    return m_manager->mk_func_decl(symbol(name), arity, domain, range,
                                   func_decl_info(m_family_id, k));
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                          unsigned arity, sort* const* domain, sort* range) {
    ast_manager& m = *m_manager;
    arith_util a(m);
    std::stringstream msg;
    if (num_parameters != 0) {
        msg << "date operations do not take parameters";
        m.raise_exception(msg.str());
        return nullptr;
    }
    auto check_arity = [&](unsigned expected) {
        if (arity != expected) {
            msg << "incorrect number of arguments. Expected " << expected << ", received " << arity;
            m.raise_exception(msg.str());
        }
    };
    auto check_int = [&](unsigned i) {
        if (!a.is_int(domain[i])) {
            msg << "argument " << (i + 1) << " has sort " << mk_pp(domain[i], m) << ", expected Int";
            m.raise_exception(msg.str());
        }
    };
    auto check_date = [&](unsigned i) {
        if (domain[i] != m_date) {
            msg << "argument " << (i + 1) << " has sort " << mk_pp(domain[i], m) << ", expected Date";
            m.raise_exception(msg.str());
        }
    };
    switch (k) {
    case OP_DATE_MK:
        check_arity(3);
        check_int(0); check_int(1); check_int(2);
        return mk_decl(k, "date.mk", arity, domain, m_date);
    case OP_DATE_YEAR:
        check_arity(1);
        check_date(0);
        return mk_decl(k, "date.year", arity, domain, a.mk_int());
    case OP_DATE_MONTH:
        check_arity(1);
        check_date(0);
        return mk_decl(k, "date.month", arity, domain, a.mk_int());
    case OP_DATE_DAY:
        check_arity(1);
        check_date(0);
        return mk_decl(k, "date.day", arity, domain, a.mk_int());
    case OP_DATE_ADD:
        check_arity(4);
        check_date(0); check_int(1); check_int(2); check_int(3);
        return mk_decl(k, "date.add", arity, domain, m_date);
    case OP_DATE_SUB:
        check_arity(4);
        check_date(0); check_int(1); check_int(2); check_int(3);
        return mk_decl(k, "date.sub", arity, domain, m_date);
    case OP_DATE_LT:
        check_arity(2);
        check_date(0); check_date(1);
        return mk_decl(k, "date.lt", arity, domain, m.mk_bool_sort());
    case OP_DATE_LE:
        check_arity(2);
        check_date(0); check_date(1);
        return mk_decl(k, "date.le", arity, domain, m.mk_bool_sort());
    case OP_DATE_GT:
        check_arity(2);
        check_date(0); check_date(1);
        return mk_decl(k, "date.gt", arity, domain, m.mk_bool_sort());
    case OP_DATE_GE:
        check_arity(2);
        check_date(0); check_date(1);
        return mk_decl(k, "date.ge", arity, domain, m.mk_bool_sort());
    case OP_DATE_EPOCH:
        check_arity(1);
        check_date(0);
        return mk_decl(k, "date.epoch!", arity, domain, a.mk_int());
    default:
        UNREACHABLE();
        return nullptr;
    }
}

void date_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const& logic) {
    op_names.push_back(builtin_name("date.mk",    OP_DATE_MK));
    op_names.push_back(builtin_name("date.year",  OP_DATE_YEAR));
    op_names.push_back(builtin_name("date.month", OP_DATE_MONTH));
    op_names.push_back(builtin_name("date.day",   OP_DATE_DAY));
    op_names.push_back(builtin_name("date.add",   OP_DATE_ADD));
    op_names.push_back(builtin_name("date.sub",   OP_DATE_SUB));
    op_names.push_back(builtin_name("date.lt",    OP_DATE_LT));
    op_names.push_back(builtin_name("date.le",    OP_DATE_LE));
    op_names.push_back(builtin_name("date.gt",    OP_DATE_GT));
    op_names.push_back(builtin_name("date.ge",    OP_DATE_GE));
    // OP_DATE_EPOCH is internal and not exposed.
}

void date_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) {
    sort_names.push_back(builtin_name("Date", DATE_SORT));
}

bool date_decl_plugin::is_value(app* e) const {
    date_util u(*m_manager);
    return u.is_date_value(e);
}

bool date_decl_plugin::is_unique_value(app* e) const {
    // canonical date values are in bijection with epoch day numbers
    return is_value(e);
}

bool date_decl_plugin::are_equal(app* a, app* b) const {
    return a == b;
}

bool date_decl_plugin::are_distinct(app* a, app* b) const {
    return a != b && is_value(a) && is_value(b);
}

expr* date_decl_plugin::get_some_value(sort* s) {
    date_util u(*m_manager);
    return u.mk_date_value(rational(0));
}

// --------------------------------------------------------------------------
// date_util - term construction and recognition

app* date_util::mk_mk(expr* y, expr* mo, expr* d) {
    expr* args[3] = { y, mo, d };
    return m.mk_app(m_fid, OP_DATE_MK, 3, args);
}

app* date_util::mk_epoch(expr* d) {
    return m.mk_app(m_fid, OP_DATE_EPOCH, 1, &d);
}

app* date_util::mk_year(expr* d) {
    return m.mk_app(m_fid, OP_DATE_YEAR, 1, &d);
}

app* date_util::mk_month(expr* d) {
    return m.mk_app(m_fid, OP_DATE_MONTH, 1, &d);
}

app* date_util::mk_day(expr* d) {
    return m.mk_app(m_fid, OP_DATE_DAY, 1, &d);
}

expr_ref date_util::mk_ineg(expr* e) {
    rational r;
    if (m_arith.is_numeral(e, r))
        return expr_ref(m_arith.mk_int(-r), m);
    return expr_ref(m_arith.mk_uminus(e), m);
}

app* date_util::mk_date_value(rational const& epoch) {
    rational y, mo, d;
    civil_of_epoch(epoch, y, mo, d);
    expr* args[3] = { m_arith.mk_int(y), m_arith.mk_int(mo), m_arith.mk_int(d) };
    return m.mk_app(m_fid, OP_DATE_MK, 3, args);
}

bool date_util::is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d) const {
    if (!is_mk(e))
        return false;
    app const* a = to_app(e);
    arith_util& au = const_cast<date_util*>(this)->m_arith;
    return
        au.is_numeral(a->get_arg(0), y) && y.is_int() &&
        au.is_numeral(a->get_arg(1), mo) && mo.is_int() &&
        au.is_numeral(a->get_arg(2), d) && d.is_int();
}

bool date_util::is_date_value(expr const* e, rational& epoch) const {
    rational y, mo, d;
    if (!is_numeral_mk(e, y, mo, d))
        return false;
    if (!is_valid_civil(y, mo, d))
        return false;
    epoch = days_from_civil(y, mo, d);
    return true;
}

// --------------------------------------------------------------------------
// concrete calendar arithmetic

bool date_util::is_leap_year(rational const& y) {
    rational const r4(4), r100(100), r400(400);
    if (!mod(y, r4).is_zero())
        return false;
    return !mod(y, r100).is_zero() || mod(y, r400).is_zero();
}

rational date_util::days_in_month(rational const& y, rational const& mo) {
    SASSERT(rational(1) <= mo && mo <= rational(12));
    unsigned m = mo.get_unsigned();
    switch (m) {
    case 2:
        return rational(is_leap_year(y) ? 29 : 28);
    case 4: case 6: case 9: case 11:
        return rational(30);
    default:
        return rational(31);
    }
}

bool date_util::is_valid_civil(rational const& y, rational const& mo, rational const& d) {
    return rational(1) <= mo && mo <= rational(12) &&
           rational(1) <= d && d <= days_in_month(y, mo);
}

rational date_util::days_from_civil(rational const& y, rational const& mo, rational const& d) {
    SASSERT(rational(1) <= mo && mo <= rational(12));
    rational const r4(4), r5(5), r100(100), r400(400);
    rational yp  = (mo <= rational(2)) ? y - rational(1) : y;
    rational era = div(yp, r400);
    rational yoe = yp - r400 * era;                                   // [0, 399]
    rational mp  = (mo >= rational(3)) ? mo - rational(3) : mo + rational(9); // [0, 11]
    rational doy = div(rational(153) * mp + rational(2), r5) + d - rational(1);
    rational doe = rational(365) * yoe + div(yoe, r4) - div(yoe, r100) + doy;
    return rational(146097) * era + doe - rational(719468);
}

void date_util::civil_of_epoch(rational const& z, rational& y, rational& mo, rational& d) {
    rational const r4(4), r5(5), r100(100);
    rational zp  = z + rational(719468);
    rational era = div(zp, rational(146097));
    rational doe = zp - rational(146097) * era;                       // [0, 146096]
    rational yoe = div(doe - div(doe, rational(1460)) + div(doe, rational(36524)) - div(doe, rational(146096)),
                       rational(365));                                // [0, 399]
    rational y1  = yoe + rational(400) * era;
    rational doy = doe - (rational(365) * yoe + div(yoe, r4) - div(yoe, r100)); // [0, 365]
    rational mp  = div(r5 * doy + rational(2), rational(153));        // [0, 11]
    d  = doy - div(rational(153) * mp + rational(2), r5) + rational(1);
    mo = (mp < rational(10)) ? mp + rational(3) : mp - rational(9);
    y  = (mo <= rational(2)) ? y1 + rational(1) : y1;
}

rational date_util::add_to_epoch(rational const& z, rational const& py, rational const& pm, rational const& pd) {
    rational const r12(12);
    rational y, mo, d;
    civil_of_epoch(z, y, mo, d);
    rational mo_total = r12 * (y + py) + (mo - rational(1)) + pm;
    rational yy = div(mo_total, r12);
    rational mm = mod(mo_total, r12) + rational(1);
    rational len = days_in_month(yy, mm);
    rational dd = (d <= len) ? d : len;
    return days_from_civil(yy, mm, dd) + pd;
}

// --------------------------------------------------------------------------
// symbolic encodings

expr_ref date_util::mk_num(int n) {
    return expr_ref(m_arith.mk_int(n), m);
}

expr_ref date_util::mk_num(rational const& r) {
    return expr_ref(m_arith.mk_int(r), m);
}

expr_ref date_util::mk_idiv(expr* x, int c) {
    return expr_ref(m_arith.mk_idiv(x, m_arith.mk_int(c)), m);
}

expr_ref date_util::mk_imod(expr* x, int c) {
    return expr_ref(m_arith.mk_mod(x, m_arith.mk_int(c)), m);
}

expr_ref date_util::mk_jan_feb_flag(expr* mo) {
    // 0/1 indicator of mo <= 2. The ite is confined to this tiny term so
    // that the shifted year and the month offset stay *linear* in mo and
    // the flag: with the cut 0 <= flag <= 1 asserted, the LP relaxation
    // keeps epoch and components coupled before the condition is decided,
    // where an ite over the full subterm leaves them disconnected.
    arith_util& a = m_arith;
    return expr_ref(m.mk_ite(a.mk_le(mo, mk_num(2)), mk_num(1), mk_num(0)), m);
}

expr_ref date_util::mk_month_offset(expr* mo) {
    // day-of-year of the first day of month mo relative to March 1:
    // Hinnant's (153*mp + 2)/5 with mp = (mo + 9) mod 12, written
    // linearly as mp = mo - 3 + 12*flag. The div form is kept (rather
    // than a 12-way ite table) because its LP relaxation is tight:
    // moff ~ 30.6*mp pins the month during model search, where an ite
    // table costs blind Boolean case splits.
    arith_util& a = m_arith;
    expr_ref b2 = mk_jan_feb_flag(mo);
    expr_ref m3 = mk_num(-3);
    expr_ref b12(a.mk_mul(mk_num(12), b2), m);
    expr* mp_args[3] = { mo, m3, b12 };
    expr_ref mp(a.mk_add(3, mp_args), m);
    return mk_idiv(a.mk_add(a.mk_mul(mk_num(153), mp), mk_num(2)), 5);
}

expr_ref date_util::mk_days_from_civil(expr* y, expr* mo, expr* d) {
    arith_util& a = m_arith;
    // Hinnant's algorithm with the era/year-of-era split eliminated:
    // 146097*era + 365*yoe + yoe/4 - yoe/100 with era = yp/400 and
    // yoe = yp - 400*era collapses to 365*yp + yp/4 - yp/100 + yp/400
    // (the divisions are Euclidean = floor, the divisors are positive).
    // Only three div terms remain, all over the same shifted year.
    expr_ref b2 = mk_jan_feb_flag(mo);
    expr_ref yp(a.mk_sub(y, b2), m);
    expr_ref y365(a.mk_mul(mk_num(365), yp), m);
    expr_ref d4 = mk_idiv(yp, 4);
    expr_ref nd100(a.mk_mul(mk_num(-1), mk_idiv(yp, 100)), m);
    expr_ref d400 = mk_idiv(yp, 400);
    expr_ref moff = mk_month_offset(mo);
    expr_ref c = mk_num(-719469); // -719468 for the epoch shift, -1 for d starting at 1
    expr* args[7] = { y365, d4, nd100, d400, moff, d, c };
    return expr_ref(a.mk_add(7, args), m);
}

expr_ref date_util::mk_days_in_month(expr* y, expr* mo) {
    expr_ref is_leap(m.mk_or(m.mk_and(m.mk_eq(mk_imod(y, 4), mk_num(0)),
                                      m.mk_not(m.mk_eq(mk_imod(y, 100), mk_num(0)))),
                             m.mk_eq(mk_imod(y, 400), mk_num(0))), m);
    expr_ref feb(m.mk_ite(is_leap, mk_num(29), mk_num(28)), m);
    expr_ref short_month(m.mk_or(m.mk_eq(mo, mk_num(4)), m.mk_eq(mo, mk_num(6)),
                                 m.mk_eq(mo, mk_num(9)), m.mk_eq(mo, mk_num(11))), m);
    return expr_ref(m.mk_ite(m.mk_eq(mo, mk_num(2)), feb,
                             m.mk_ite(short_month, mk_num(30), mk_num(31))), m);
}

void date_util::mk_civil_cuts(expr* y, expr* mo, expr_ref_vector& cuts) {
    arith_util& a = m_arith;
    // tautological bounds over the ite terms of the civil encoding.
    // Each ite variable has no LP row until its condition is assigned;
    // these cuts keep the relaxation bounded from the start.
    expr_ref b2 = mk_jan_feb_flag(mo);
    cuts.push_back(a.mk_ge(b2, mk_num(0)));
    cuts.push_back(a.mk_le(b2, mk_num(1)));
    expr_ref dim = mk_days_in_month(y, mo);
    cuts.push_back(a.mk_ge(dim, mk_num(28)));
    cuts.push_back(a.mk_le(dim, mk_num(31)));
}

void date_util::month_span_bounds(rational const& s, rational& lo, rational& hi) {
    static const int min_len[12] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 };
    rational const r12(12);
    rational abs_s = abs(s);
    rational q = div(abs_s, r12);
    unsigned r = (abs_s - r12 * q).get_unsigned(); // 0 <= r < 12
    int minr = 0, maxr = 0;
    if (r > 0) {
        minr = INT_MAX;
        maxr = INT_MIN;
        for (unsigned st = 0; st < 12; ++st) {
            int mn = 0, mx = 0;
            for (unsigned i = 0; i < r; ++i) {
                unsigned mi = (st + i) % 12;
                mn += min_len[mi];
                mx += min_len[mi] + (mi == 1 ? 1 : 0); // Feb may have 29 days
            }
            minr = std::min(minr, mn);
            maxr = std::max(maxr, mx);
        }
    }
    // the months between the base and the shifted first-of-month form
    // |s| consecutive months: any block of 12 consecutive months spans
    // 365 or 366 days (it contains exactly one February), the remaining
    // r months span between the shortest and the longest r-month window.
    // The end-of-month clamp lowers the day of the result by at most 3
    // (day <= 31, month length >= 28), in both shift directions.
    rational sum_lo = rational(365) * q + rational(minr);
    rational sum_hi = rational(366) * q + rational(maxr);
    if (s.is_neg()) {
        lo = -sum_hi - rational(3);
        hi = -sum_lo;
    }
    else {
        lo = sum_lo - rational(3);
        hi = sum_hi;
    }
}

bool date_util::is_zero_month_shift(expr* py, expr* pm) const {
    arith_util& a = const_cast<date_util*>(this)->m_arith;
    rational ry, rm;
    return a.is_extended_numeral(py, ry) && ry.is_zero() &&
           a.is_extended_numeral(pm, rm) && rm.is_zero();
}

bool date_util::is_zero(expr* e) const {
    arith_util& a = const_cast<date_util*>(this)->m_arith;
    rational r;
    return a.is_extended_numeral(e, r) && r.is_zero();
}

expr_ref date_util::mk_month_total(expr* y, expr* mo) {
    return expr_ref(m_arith.mk_add(m_arith.mk_mul(mk_num(12), y), mo), m);
}

expr_ref date_util::mk_clamped_day(expr* dd, expr* y, expr* mo) {
    arith_util& a = m_arith;
    expr_ref len = mk_days_in_month(y, mo);
    // clamp condition in bound form (term <= numeral): with len an ite
    // term, (<= dd len) would be normalized with the ite on the
    // right-hand side, a shape the legacy arithmetic solver does not
    // internalize (it lands in m_not_handled and final check gives up)
    expr_ref no_clamp(a.mk_le(a.mk_sub(dd, len), mk_num(0)), m);
    return expr_ref(m.mk_ite(no_clamp, dd, len), m);
}
