/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declarations for the theory of calendar dates.

Author:

    Angel Cui 2026-03-23

--*/
#include "ast/date_decl_plugin.h"
#include "ast/ast_pp.h"

static unsigned const g_days_in_month[13]   = { 0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 };
static unsigned const g_days_before_month[13] = { 0, 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334 };

date_decl_plugin::~date_decl_plugin() {
    if (m_manager) {
        m_manager->dec_ref(m_date);
        m_manager->dec_ref(m_int);
    }
}

void date_decl_plugin::set_manager(ast_manager* m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_date = m->mk_sort(symbol("Date"), sort_info(m_family_id, DATE_SORT));
    m->inc_ref(m_date);
}

sort* date_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) {
    if (k != DATE_SORT || num_parameters != 0) {
        m_manager->raise_exception("unknown date sort");
        return nullptr;
    }
    return m_date;
}

func_decl* date_decl_plugin::mk_date_op(decl_kind k, char const* name, unsigned arity, sort* const* domain, sort* range) {
    return m_manager->mk_func_decl(symbol(name), arity, domain, range, func_decl_info(m_family_id, k));
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                          unsigned arity, sort* const* domain, sort* range) {
    ast_manager& m = *m_manager;
    if (!m_int) {
        arith_util a(m);
        m_int = a.mk_int();
        m.inc_ref(m_int);
    }
    std::stringstream msg;
    if (num_parameters != 0) {
        msg << "date operators expect no parameters";
        m.raise_exception(msg.str());
    }
    auto check = [&](unsigned expected_arity, std::initializer_list<sort*> expected) {
        if (arity != expected_arity) {
            msg << "incorrect number of arguments passed. Expected " << expected_arity << ", received " << arity;
            m.raise_exception(msg.str());
        }
        unsigned i = 0;
        for (sort* s : expected) {
            if (domain[i] != s) {
                msg << "incorrect sort of argument " << i << ": " << mk_pp(domain[i], m) << " expected " << mk_pp(s, m);
                m.raise_exception(msg.str());
            }
            ++i;
        }
    };
    switch (k) {
    case OP_DATE_MK:
        check(3, { m_int, m_int, m_int });
        return mk_date_op(k, "date.mk", arity, domain, m_date);
    case OP_DATE_YEAR:
        check(1, { m_date });
        return mk_date_op(k, "date.year", arity, domain, m_int);
    case OP_DATE_MONTH:
        check(1, { m_date });
        return mk_date_op(k, "date.month", arity, domain, m_int);
    case OP_DATE_DAY:
        check(1, { m_date });
        return mk_date_op(k, "date.day", arity, domain, m_int);
    case OP_DATE_ADD:
        check(4, { m_date, m_int, m_int, m_int });
        return mk_date_op(k, "date.add", arity, domain, m_date);
    case OP_DATE_SUB:
        check(4, { m_date, m_int, m_int, m_int });
        return mk_date_op(k, "date.sub", arity, domain, m_date);
    case OP_DATE_LT:
        check(2, { m_date, m_date });
        return mk_date_op(k, "date.lt", arity, domain, m.mk_bool_sort());
    case OP_DATE_LE:
        check(2, { m_date, m_date });
        return mk_date_op(k, "date.le", arity, domain, m.mk_bool_sort());
    case OP_DATE_GT:
        check(2, { m_date, m_date });
        return mk_date_op(k, "date.gt", arity, domain, m.mk_bool_sort());
    case OP_DATE_GE:
        check(2, { m_date, m_date });
        return mk_date_op(k, "date.ge", arity, domain, m.mk_bool_sort());
    default:
        UNREACHABLE();
        return nullptr;
    }
}

void date_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const& logic) {
    op_names.push_back(builtin_name("date.mk", OP_DATE_MK));
    op_names.push_back(builtin_name("date.year", OP_DATE_YEAR));
    op_names.push_back(builtin_name("date.month", OP_DATE_MONTH));
    op_names.push_back(builtin_name("date.day", OP_DATE_DAY));
    op_names.push_back(builtin_name("date.add", OP_DATE_ADD));
    op_names.push_back(builtin_name("date.sub", OP_DATE_SUB));
    op_names.push_back(builtin_name("date.lt", OP_DATE_LT));
    op_names.push_back(builtin_name("date.le", OP_DATE_LE));
    op_names.push_back(builtin_name("date.gt", OP_DATE_GT));
    op_names.push_back(builtin_name("date.ge", OP_DATE_GE));
}

void date_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) {
    sort_names.push_back(builtin_name("Date", DATE_SORT));
}

bool date_decl_plugin::is_value(app* e) const {
    date_util u(*m_manager);
    return u.is_value_mk(e);
}

bool date_decl_plugin::is_unique_value(app* e) const {
    // valid numeral triples are canonical: distinct triples denote distinct dates
    return is_value(e);
}

bool date_decl_plugin::are_equal(app* a, app* b) const {
    return a == b;
}

bool date_decl_plugin::are_distinct(app* a, app* b) const {
    return a != b && is_value(a) && is_value(b);
}

expr* date_decl_plugin::get_some_value(sort* s) {
    SASSERT(s == m_date);
    date_util u(*m_manager);
    arith_util a(*m_manager);
    return u.mk_mk(a.mk_int(1), a.mk_int(1), a.mk_int(1));
}

// ----------------------------------------------------------------------
// date_util
// ----------------------------------------------------------------------

date_util::date_util(ast_manager& m):
    m(m),
    m_fid(m.mk_family_id("date")),
    m_arith(m) {
    m_plugin = static_cast<date_decl_plugin*>(m.get_plugin(m_fid));
}

app* date_util::mk_mk(expr* y, expr* mo, expr* d) {
    expr* args[3] = { y, mo, d };
    return m.mk_app(m_fid, OP_DATE_MK, 3, args);
}

app* date_util::mk_add(expr* d, expr* py, expr* pm, expr* pd) {
    expr* args[4] = { d, py, pm, pd };
    return m.mk_app(m_fid, OP_DATE_ADD, 4, args);
}

bool date_util::is_selector_mk(expr const* e) const {
    expr* s0 = nullptr, * s1 = nullptr, * s2 = nullptr;
    return is_mk(e) &&
        is_year(to_app(e)->get_arg(0), s0) &&
        is_month(to_app(e)->get_arg(1), s1) &&
        is_day(to_app(e)->get_arg(2), s2) &&
        s0 == s1 && s1 == s2;
}

bool date_util::is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d) const {
    return is_mk(e) &&
        m_arith.is_numeral(to_app(e)->get_arg(0), y) &&
        m_arith.is_numeral(to_app(e)->get_arg(1), mo) &&
        m_arith.is_numeral(to_app(e)->get_arg(2), d);
}

bool date_util::is_value_mk(expr const* e, rational& y, rational& mo, rational& d) const {
    return is_numeral_mk(e, y, mo, d) && is_valid_date(y, mo, d);
}

bool date_util::is_value_mk(expr const* e) const {
    rational y, mo, d;
    return is_value_mk(e, y, mo, d);
}

// ----------------------------------------------------------------------
// concrete calendar arithmetic
// ----------------------------------------------------------------------

bool date_util::is_leap_year(rational const& y) {
    rational const four(4), hundred(100), four_hundred(400);
    return (mod(y, four).is_zero() && !mod(y, hundred).is_zero()) || mod(y, four_hundred).is_zero();
}

unsigned date_util::days_in_month(rational const& y, unsigned mo) {
    SASSERT(1 <= mo && mo <= 12);
    if (mo == 2 && is_leap_year(y))
        return 29;
    return g_days_in_month[mo];
}

bool date_util::is_valid_date(rational const& y, rational const& mo, rational const& d) {
    if (!y.is_int() || !mo.is_int() || !d.is_int())
        return false;
    if (mo < rational(1) || mo > rational(12))
        return false;
    unsigned m_val = mo.get_unsigned();
    return rational(1) <= d && d <= rational(days_in_month(y, m_val));
}

rational date_util::rata_die(rational const& y, unsigned mo, rational const& d) {
    SASSERT(1 <= mo && mo <= 12);
    rational const four(4), hundred(100), four_hundred(400);
    rational ym1 = y - rational(1);
    rational days_before_year = rational(365) * ym1 + div(ym1, four) - div(ym1, hundred) + div(ym1, four_hundred);
    rational result = days_before_year + rational(g_days_before_month[mo]) + d;
    if (mo > 2 && is_leap_year(y))
        result += rational(1);
    return result;
}

void date_util::rata_die_inv(rational const& n, rational& y, unsigned& mo, rational& d) {
    rational const cycle(146097); // days in 400 Gregorian years
    y = div(rational(400) * n, cycle) + rational(1);
    while (rata_die(y, 1, rational(1)) > n)
        y -= rational(1);
    while (rata_die(y + rational(1), 1, rational(1)) <= n)
        y += rational(1);
    rational doy = n - rata_die(y, 1, rational(1)) + rational(1);
    SASSERT(rational(1) <= doy && doy <= rational(is_leap_year(y) ? 366 : 365));
    mo = 1;
    while (doy > rational(days_in_month(y, mo))) {
        doy -= rational(days_in_month(y, mo));
        ++mo;
    }
    d = doy;
}

void date_util::add_period(rational const& y, rational const& mo, rational const& d,
                           rational const& py, rational const& pm, rational const& pd,
                           rational& oy, rational& om, rational& od) {
    SASSERT(is_valid_date(y, mo, d));
    rational const twelve(12);
    // Step 1 -- month normalization
    rational t = mo + twelve * py + pm - rational(1);
    oy = y + div(t, twelve);
    unsigned om_val = mod(t, twelve).get_unsigned() + 1;
    // Step 2 -- end-of-month clamp
    rational cd = std::min(d, rational(days_in_month(oy, om_val)));
    // Step 3 -- day carry, computed as a Rata Die shift
    rational n = rata_die(oy, om_val, cd) + pd;
    rata_die_inv(n, oy, om_val, od);
    om = rational(om_val);
}

// ----------------------------------------------------------------------
// symbolic axiom building
// ----------------------------------------------------------------------

expr_ref date_util::mk_is_leap(expr* y) {
    arith_util& a = m_arith;
    expr_ref div4(m.mk_eq(a.mk_mod(y, a.mk_int(4)), a.mk_int(0)), m);
    expr_ref div100(m.mk_eq(a.mk_mod(y, a.mk_int(100)), a.mk_int(0)), m);
    expr_ref div400(m.mk_eq(a.mk_mod(y, a.mk_int(400)), a.mk_int(0)), m);
    return expr_ref(m.mk_or(m.mk_and(div4, m.mk_not(div100)), div400), m);
}

expr_ref date_util::mk_days_in_month(expr* y, expr* mo) {
    arith_util& a = m_arith;
    expr_ref feb(m.mk_ite(mk_is_leap(y), a.mk_int(29), a.mk_int(28)), m);
    expr_ref is30(m.mk_or(m.mk_eq(mo, a.mk_int(4)), m.mk_eq(mo, a.mk_int(6)),
                          m.mk_eq(mo, a.mk_int(9)), m.mk_eq(mo, a.mk_int(11))), m);
    expr_ref other(m.mk_ite(is30, a.mk_int(30), a.mk_int(31)), m);
    return expr_ref(m.mk_ite(m.mk_eq(mo, a.mk_int(2)), feb, other), m);
}

expr* date_util::mk_ge1_le(expr* x, unsigned hi) {
    arith_util& a = m_arith;
    return m.mk_and(a.mk_le(a.mk_int(1), x), a.mk_le(x, a.mk_int(hi)));
}

expr_ref date_util::mk_is_valid(expr* y, expr* mo, expr* d) {
    arith_util& a = m_arith;
    expr_ref dim = mk_days_in_month(y, mo);
    return expr_ref(m.mk_and(mk_ge1_le(mo, 12),
                             a.mk_le(a.mk_int(1), d),
                             a.mk_le(d, dim)), m);
}

expr_ref date_util::mk_rata_die(expr* y, expr* mo, expr* d) {
    arith_util& a = m_arith;
    expr_ref ym1(a.mk_sub(y, a.mk_int(1)), m);
    expr_ref days_before_year(a.mk_add(a.mk_mul(a.mk_int(365), ym1),
                                       a.mk_idiv(ym1, a.mk_int(4)),
                                       a.mk_sub(a.mk_idiv(ym1, a.mk_int(400)),
                                                a.mk_idiv(ym1, a.mk_int(100)))), m);
    expr_ref days_before_month(a.mk_int(g_days_before_month[12]), m);
    for (unsigned i = 11; i >= 1; --i)
        days_before_month = m.mk_ite(m.mk_eq(mo, a.mk_int(i)), a.mk_int(g_days_before_month[i]), days_before_month);
    expr_ref leap_adj(m.mk_ite(m.mk_and(a.mk_ge(mo, a.mk_int(3)), mk_is_leap(y)),
                               a.mk_int(1), a.mk_int(0)), m);
    return expr_ref(a.mk_add(days_before_year, days_before_month, a.mk_add(leap_adj, d)), m);
}

expr_ref date_util::mk_days_in_month_concrete(expr* y, unsigned mo) {
    SASSERT(1 <= mo && mo <= 12);
    arith_util& a = m_arith;
    if (mo == 2)
        return expr_ref(m.mk_ite(mk_is_leap(y), a.mk_int(29), a.mk_int(28)), m);
    return expr_ref(a.mk_int(g_days_in_month[mo]), m);
}

void date_util::mk_add_triple(expr* yd, expr* md, expr* dd,
                              rational const& py, rational const& pm, rational const& pd,
                              expr_ref& ry, expr_ref& rm, expr_ref& rd) {
    SASSERT(abs(pd) <= mk_add_triple_bound());
    arith_util& a = m_arith;
    rational const twelve(12);
    rational c = twelve * py + pm;
    // month index i counted from year 1 month 1; i = 12 * (y - 1) + (m - 1)
    auto month_of = [&](rational const& i) {
        return mod(i, twelve).get_unsigned() + 1;
    };
    auto year_of = [&](expr* y0, rational const& i) -> expr* {
        // year of month index 12 * (y0 - 1) + i
        rational q = div(i, twelve);
        return q.is_zero() ? y0 : a.mk_add(y0, a.mk_numeral(q, true));
    };
    ry = nullptr;
    rm = nullptr;
    rd = nullptr;
    for (unsigned k = 12; k >= 1; --k) {
        // Step 1 -- month normalization: month index relative to year(d)
        rational i0 = rational(k - 1) + c;
        unsigned om = month_of(i0);
        expr_ref oy(year_of(yd, i0), m);
        // Step 2 -- end-of-month clamp
        expr_ref dim0 = mk_days_in_month_concrete(oy, om);
        expr_ref cd(m.mk_ite(a.mk_le(dd, dim0), dd, dim0), m);
        // Step 3 -- day carry: tmp = cd + pd walks across at most
        // |pd|/28 + 1 month boundaries
        expr_ref tmp(pd.is_zero() ? cd.get() : a.mk_add(cd, a.mk_numeral(pd, true)), m);
        expr_ref ky(m), km(m), kd(m);
        if (pd.is_nonneg()) {
            // months i0, i0 + 1, ... with cumulative day counts; the result
            // is the first month j with tmp <= days up to and including j
            unsigned steps = 1 + (31 + pd.get_unsigned()) / 28;
            expr_ref sum(a.mk_int(0), m);
            std::vector<std::tuple<rational, expr*, expr*>> months; // (index, days before, days upto)
            for (unsigned j = 0; j < steps; ++j) {
                rational i = i0 + rational(j);
                expr* before = sum;
                sum = a.mk_add(sum, mk_days_in_month_concrete(year_of(yd, i), month_of(i)));
                months.push_back({ i, before, sum.get() });
            }
            // fallback month is out of reach: steps months cover any carry
            rational il = i0 + rational(steps);
            ky = year_of(yd, il);
            km = a.mk_int(month_of(il));
            kd = a.mk_sub(tmp, sum);
            for (unsigned j = steps; j-- > 0; ) {
                auto const& [i, before, upto] = months[j];
                expr* in_month = a.mk_le(tmp, upto);
                ky = m.mk_ite(in_month, year_of(yd, i), ky);
                km = m.mk_ite(in_month, a.mk_int(month_of(i)), km);
                kd = m.mk_ite(in_month, a.mk_sub(tmp, before), kd);
            }
        }
        else {
            // months i0, i0 - 1, ... ; tmp_j = tmp + days of the j months
            // before i0; the result is the first month with tmp_j >= 1
            unsigned steps = 2 + (-pd).get_unsigned() / 28;
            std::vector<std::pair<rational, expr*>> months; // (index, tmp_j)
            expr_ref tmpj(tmp, m);
            months.push_back({ i0, tmpj.get() });
            for (unsigned j = 1; j < steps; ++j) {
                rational i = i0 - rational(j);
                tmpj = a.mk_add(tmpj, mk_days_in_month_concrete(year_of(yd, i), month_of(i)));
                months.push_back({ i, tmpj.get() });
            }
            auto const& [il, tl] = months.back();
            ky = year_of(yd, il);
            km = a.mk_int(month_of(il));
            kd = tl;
            for (unsigned j = months.size() - 1; j-- > 0; ) {
                auto const& [i, tj] = months[j];
                expr* in_month = a.mk_ge(tj, a.mk_int(1));
                ky = m.mk_ite(in_month, year_of(yd, i), ky);
                km = m.mk_ite(in_month, a.mk_int(month_of(i)), km);
                kd = m.mk_ite(in_month, tj, kd);
            }
        }
        if (!ry) {
            ry = ky;
            rm = km;
            rd = kd;
        }
        else {
            expr_ref is_k(m.mk_eq(md, a.mk_numeral(rational(k), true)), m);
            ry = m.mk_ite(is_k, ky, ry);
            rm = m.mk_ite(is_k, km, rm);
            rd = m.mk_ite(is_k, kd, rd);
        }
    }
}

expr_ref date_util::mk_add_rata_die(expr* yd, expr* md, expr* dd, expr* py, expr* pm, expr* pd) {
    arith_util& a = m_arith;
    rational rpy, rpm;
    if (a.is_numeral(py, rpy) && a.is_numeral(pm, rpm) && rpy.is_int() && rpm.is_int()) {
        // concrete period: a case split on the month avoids div/mod terms
        rational const twelve(12);
        rational c = twelve * rpy + rpm;
        expr_ref result(m);
        for (unsigned k = 12; k >= 1; --k) {
            rational t = rational(k - 1) + c;
            rational q = div(t, twelve);
            expr_ref oy(q.is_zero() ? yd : a.mk_add(yd, a.mk_numeral(q, true)), m);
            expr_ref om(a.mk_numeral(mod(t, twelve) + rational(1), true), m);
            expr_ref dim = mk_days_in_month(oy, om);
            expr_ref cd(m.mk_ite(a.mk_le(dd, dim), dd, dim), m);
            expr_ref branch(a.mk_add(mk_rata_die(oy, om, cd), pd), m);
            if (!result)
                result = branch;
            else
                result = m.mk_ite(m.mk_eq(md, a.mk_numeral(rational(k), true)), branch, result);
        }
        return result;
    }
    // Step 1 -- month normalization
    expr_ref t(a.mk_sub(a.mk_add(md, a.mk_mul(a.mk_int(12), py), pm), a.mk_int(1)), m);
    expr_ref oy(a.mk_add(yd, a.mk_idiv(t, a.mk_int(12))), m);
    expr_ref om(a.mk_add(a.mk_mod(t, a.mk_int(12)), a.mk_int(1)), m);
    // Step 2 -- end-of-month clamp
    expr_ref dim = mk_days_in_month(oy, om);
    expr_ref cd(m.mk_ite(a.mk_le(dd, dim), dd, dim), m);
    // Step 3 -- day carry is a Rata Die shift by pd
    return expr_ref(a.mk_add(mk_rata_die(oy, om, cd), pd), m);
}
