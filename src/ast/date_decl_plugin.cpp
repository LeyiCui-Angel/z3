/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declarations for the theory of calendar dates.

Author:

    Claude 2026-07-04

--*/
#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"

date_decl_plugin::~date_decl_plugin() {
    if (m_manager) {
        m_manager->dec_ref(m_date);
        m_manager->dec_ref(m_int);
    }
}

void date_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_date = m->mk_sort(symbol("Date"), sort_info(m_family_id, DATE_SORT));
    m->inc_ref(m_date);
    arith_util a(*m);
    m_int = a.mk_int();
    m->inc_ref(m_int);
}

sort* date_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) {
    if (k != DATE_SORT || num_parameters != 0) {
        m_manager->raise_exception("unexpected date sort");
        return nullptr;
    }
    return m_date;
}

func_decl* date_decl_plugin::mk_date_op(decl_kind k, unsigned arity, sort* const* domain) {
    ast_manager& m = *m_manager;
    char const* name = nullptr;
    unsigned expected_arity = 0;
    sort* expected_domain[4] = { nullptr, nullptr, nullptr, nullptr };
    sort* range = nullptr;
    switch (k) {
    case OP_DATE_MK:
        name = "date.mk";
        expected_arity = 3;
        expected_domain[0] = expected_domain[1] = expected_domain[2] = m_int;
        range = m_date;
        break;
    case OP_DATE_YEAR:
    case OP_DATE_MONTH:
    case OP_DATE_DAY:
        name = k == OP_DATE_YEAR ? "date.year" : (k == OP_DATE_MONTH ? "date.month" : "date.day");
        expected_arity = 1;
        expected_domain[0] = m_date;
        range = m_int;
        break;
    case OP_DATE_ADD:
    case OP_DATE_SUB:
        name = k == OP_DATE_ADD ? "date.add" : "date.sub";
        expected_arity = 4;
        expected_domain[0] = m_date;
        expected_domain[1] = expected_domain[2] = expected_domain[3] = m_int;
        range = m_date;
        break;
    case OP_DATE_LT:
    case OP_DATE_LE:
    case OP_DATE_GT:
    case OP_DATE_GE:
        name = k == OP_DATE_LT ? "date.lt" : (k == OP_DATE_LE ? "date.le" : (k == OP_DATE_GT ? "date.gt" : "date.ge"));
        expected_arity = 2;
        expected_domain[0] = expected_domain[1] = m_date;
        range = m.mk_bool_sort();
        break;
    default:
        UNREACHABLE();
        return nullptr;
    }
    std::stringstream msg;
    if (arity != expected_arity)
        msg << name << ": incorrect number of arguments. Expected " << expected_arity << ", received " << arity;
    else {
        for (unsigned i = 0; i < arity; ++i) {
            if (domain[i] != expected_domain[i]) {
                msg << name << ": sort mismatch for argument " << (i + 1)
                    << ". Expected " << mk_pp(expected_domain[i], m)
                    << ", received " << mk_pp(domain[i], m);
                m.raise_exception(msg.str());
            }
        }
        return m.mk_func_decl(symbol(name), arity, domain, range, func_decl_info(m_family_id, k));
    }
    m.raise_exception(msg.str());
    return nullptr;
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                          unsigned arity, sort* const* domain, sort* range) {
    if (num_parameters != 0) {
        m_manager->raise_exception("date operations do not accept parameters");
        return nullptr;
    }
    return mk_date_op(k, arity, domain);
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
    rational y, mo, d;
    return u.is_value_mk(e, y, mo, d);
}

bool date_decl_plugin::is_unique_value(app* e) const {
    // canonical values are numeral date.mk applications with valid triples;
    // distinct valid triples denote distinct dates
    return is_value(e);
}

bool date_decl_plugin::are_equal(app* a, app* b) const {
    return a == b;
}

bool date_decl_plugin::are_distinct(app* a, app* b) const {
    return a != b && is_unique_value(a) && is_unique_value(b);
}

expr* date_decl_plugin::get_some_value(sort* s) {
    SASSERT(s == m_date);
    date_util u(*m_manager);
    return u.mk_date_value(rational(1), rational(1), rational(1));
}

// ---------------------------------------------------------------------
// date_util
// ---------------------------------------------------------------------

bool date_util::is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d) const {
    if (!is_mk(e))
        return false;
    app const* a = to_app(e);
    arith_util& au = const_cast<date_util*>(this)->m_arith;
    return
        au.is_numeral(a->get_arg(0), y)  && y.is_int()  &&
        au.is_numeral(a->get_arg(1), mo) && mo.is_int() &&
        au.is_numeral(a->get_arg(2), d)  && d.is_int();
}

app* date_util::mk_date_value(rational const& y, rational const& mo, rational const& d) {
    SASSERT(is_valid_date(y, mo, d));
    return mk_mk(m_arith.mk_int(y), m_arith.mk_int(mo), m_arith.mk_int(d));
}

bool date_util::is_leap_year(rational const& y) {
    return (mod(y, rational(4)).is_zero() && !mod(y, rational(100)).is_zero()) ||
           mod(y, rational(400)).is_zero();
}

rational date_util::days_in_month(rational const& y, rational const& mo) {
    SASSERT(rational(1) <= mo && mo <= rational(12));
    if (mo == rational(2))
        return rational(is_leap_year(y) ? 29 : 28);
    if (mo == rational(4) || mo == rational(6) || mo == rational(9) || mo == rational(11))
        return rational(30);
    return rational(31);
}

bool date_util::is_valid_date(rational const& y, rational const& mo, rational const& d) {
    return rational(1) <= mo && mo <= rational(12) &&
           rational(1) <= d && d <= days_in_month(y, mo);
}

rational date_util::rata_die(rational const& y, rational const& mo, rational const& d) {
    SASSERT(is_valid_date(y, mo, d));
    rational yy  = mo <= rational(2) ? y - rational(1) : y;
    rational era = div(yy, rational(400));
    rational yoe = yy - era * rational(400);
    rational mp  = mo > rational(2) ? mo - rational(3) : mo + rational(9);
    rational doy = div(rational(153) * mp + rational(2), rational(5)) + d - rational(1);
    rational doe = yoe * rational(365) + div(yoe, rational(4)) - div(yoe, rational(100)) + doy;
    return era * rational(146097) + doe - rational(719468);
}

void date_util::date_of_rata_die(rational const& rd, rational& y, rational& mo, rational& d) {
    rational z   = rd + rational(719468);
    rational era = div(z, rational(146097));
    rational doe = z - era * rational(146097);
    rational yoe = div(doe - div(doe, rational(1460)) + div(doe, rational(36524)) - div(doe, rational(146096)),
                       rational(365));
    rational doy = doe - (rational(365) * yoe + div(yoe, rational(4)) - div(yoe, rational(100)));
    rational mp  = div(rational(5) * doy + rational(2), rational(153));
    d  = doy - div(rational(153) * mp + rational(2), rational(5)) + rational(1);
    mo = mp < rational(10) ? mp + rational(3) : mp - rational(9);
    y  = yoe + era * rational(400) + (mo <= rational(2) ? rational(1) : rational(0));
    SASSERT(is_valid_date(y, mo, d));
    SASSERT(rata_die(y, mo, d) == rd);
}

void date_util::add_period(rational const& y, rational const& mo, rational const& d,
                           rational const& py, rational const& pm, rational const& pd,
                           rational& ry, rational& rm, rational& rd) {
    SASSERT(is_valid_date(y, mo, d));
    // step 1 -- month normalization
    rational t  = mo + rational(12) * py + pm - rational(1);
    rational oy = y + div(t, rational(12));
    rational om = mod(t, rational(12)) + rational(1);
    // step 2 -- end-of-month clamp
    rational cd = std::min(d, days_in_month(oy, om));
    // step 3 -- day carry, computed via the day-number bijection
    date_of_rata_die(rata_die(oy, om, cd) + pd, ry, rm, rd);
}

expr_ref date_util::mk_is_leap_expr(expr* y) {
    expr_ref div4(m.mk_eq(m_arith.mk_mod(y, m_arith.mk_int(4)), m_arith.mk_int(0)), m);
    expr_ref div100(m.mk_eq(m_arith.mk_mod(y, m_arith.mk_int(100)), m_arith.mk_int(0)), m);
    expr_ref div400(m.mk_eq(m_arith.mk_mod(y, m_arith.mk_int(400)), m_arith.mk_int(0)), m);
    return expr_ref(m.mk_or(m.mk_and(div4, m.mk_not(div100)), div400), m);
}

expr_ref date_util::mk_days_in_month_expr(expr* y, expr* mo) {
    expr_ref is_feb(m.mk_eq(mo, m_arith.mk_int(2)), m);
    expr_ref is_short(m.mk_or(m.mk_eq(mo, m_arith.mk_int(4)),
                              m.mk_eq(mo, m_arith.mk_int(6)),
                              m.mk_eq(mo, m_arith.mk_int(9)),
                              m.mk_eq(mo, m_arith.mk_int(11))), m);
    expr_ref feb_days(m.mk_ite(mk_is_leap_expr(y), m_arith.mk_int(29), m_arith.mk_int(28)), m);
    return expr_ref(m.mk_ite(is_feb, feb_days,
                             m.mk_ite(is_short, m_arith.mk_int(30), m_arith.mk_int(31))), m);
}

expr_ref date_util::mk_valid_expr(expr* y, expr* mo, expr* d) {
    ptr_buffer<expr> args;
    args.push_back(m_arith.mk_le(m_arith.mk_int(1), mo));
    args.push_back(m_arith.mk_le(mo, m_arith.mk_int(12)));
    args.push_back(m_arith.mk_le(m_arith.mk_int(1), d));
    args.push_back(m_arith.mk_le(d, mk_days_in_month_expr(y, mo)));
    return expr_ref(m.mk_and(args), m);
}

expr_ref date_util::mk_rata_die_expr(expr* y, expr* mo, expr* d) {
    arith_util& a = m_arith;
    // yy  = y - (mo <= 2 ? 1 : 0)
    expr_ref yy(a.mk_sub(y, m.mk_ite(a.mk_le(mo, a.mk_int(2)), a.mk_int(1), a.mk_int(0))), m);
    // era = yy div 400, yoe = yy mod 400
    expr_ref era(a.mk_idiv(yy, a.mk_int(400)), m);
    expr_ref yoe(a.mk_mod(yy, a.mk_int(400)), m);
    // mp  = mo + (mo > 2 ? -3 : 9)
    expr_ref mp(a.mk_add(mo, m.mk_ite(a.mk_gt(mo, a.mk_int(2)), a.mk_int(-3), a.mk_int(9))), m);
    // doy = (153*mp + 2) div 5 + d - 1
    expr_ref doy(a.mk_add(a.mk_idiv(a.mk_add(a.mk_mul(a.mk_int(153), mp), a.mk_int(2)), a.mk_int(5)),
                          d, a.mk_int(-1)), m);
    // doe = yoe*365 + yoe div 4 - yoe div 100 + doy
    expr* doe_args[4] = {
        a.mk_mul(yoe, a.mk_int(365)),
        a.mk_idiv(yoe, a.mk_int(4)),
        a.mk_mul(a.mk_int(-1), a.mk_idiv(yoe, a.mk_int(100))),
        doy
    };
    expr_ref doe(a.mk_add(4, doe_args), m);
    // era*146097 + doe - 719468
    return expr_ref(a.mk_add(a.mk_mul(era, a.mk_int(146097)), doe, a.mk_int(-719468)), m);
}

expr_ref date_util::mk_add_rata_die_expr(expr* y, expr* mo, expr* d, expr* py, expr* pm, expr* pd) {
    arith_util& a = m_arith;
    // step 1 -- month normalization: t = mo + 12*py + pm - 1
    expr* t_args[4] = { mo, a.mk_mul(a.mk_int(12), py), pm, a.mk_int(-1) };
    expr_ref t(a.mk_add(4, t_args), m);
    expr_ref oy(a.mk_add(y, a.mk_idiv(t, a.mk_int(12))), m);
    expr_ref om(a.mk_add(a.mk_mod(t, a.mk_int(12)), a.mk_int(1)), m);
    // step 2 -- end-of-month clamp
    expr_ref dim(mk_days_in_month_expr(oy, om), m);
    expr_ref clamp(m.mk_ite(a.mk_le(d, dim), d, dim), m);
    // step 3 -- day carry via the day-number bijection
    return expr_ref(a.mk_add(mk_rata_die_expr(oy, om, clamp), pd), m);
}
