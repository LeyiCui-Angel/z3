/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declaration plugin for the theory of calendar dates.

Author:

    Z3 date theory extension 2026-07-05

--*/
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

expr_ref date_util::mk_days_from_civil(expr* y, expr* mo, expr* d) {
    arith_util& a = m_arith;
    expr_ref yp(m.mk_ite(a.mk_le(mo, mk_num(2)), a.mk_sub(y, mk_num(1)), y), m);
    expr_ref era = mk_idiv(yp, 400);
    expr_ref yoe(a.mk_sub(yp, a.mk_mul(mk_num(400), era)), m);
    expr_ref mp(a.mk_add(mo, m.mk_ite(a.mk_ge(mo, mk_num(3)), mk_num(-3), mk_num(9))), m);
    expr_ref doy(a.mk_add(mk_idiv(a.mk_add(a.mk_mul(mk_num(153), mp), mk_num(2)), 5),
                          a.mk_sub(d, mk_num(1))), m);
    expr_ref doe(a.mk_add(a.mk_mul(mk_num(365), yoe),
                          a.mk_sub(mk_idiv(yoe, 4), mk_idiv(yoe, 100)),
                          doy), m);
    return expr_ref(a.mk_add(a.mk_mul(mk_num(146097), era), doe, mk_num(-719468)), m);
}

void date_util::mk_civil_of_epoch(expr* z, civil_expr& c) {
    arith_util& a = m_arith;
    expr_ref zp(a.mk_add(z, mk_num(719468)), m);
    expr_ref era = mk_idiv(zp, 146097);
    expr_ref doe(a.mk_sub(zp, a.mk_mul(mk_num(146097), era)), m);
    expr_ref yoe = mk_idiv(a.mk_add(doe,
                                    a.mk_sub(mk_idiv(doe, 36524),
                                             a.mk_add(mk_idiv(doe, 1460), mk_idiv(doe, 146096)))),
                           365);
    expr_ref y1(a.mk_add(yoe, a.mk_mul(mk_num(400), era)), m);
    expr_ref doy(a.mk_sub(doe, a.mk_add(a.mk_mul(mk_num(365), yoe),
                                        a.mk_sub(mk_idiv(yoe, 4), mk_idiv(yoe, 100)))), m);
    expr_ref mp = mk_idiv(a.mk_add(a.mk_mul(mk_num(5), doy), mk_num(2)), 153);
    c.d = a.mk_add(a.mk_sub(doy, mk_idiv(a.mk_add(a.mk_mul(mk_num(153), mp), mk_num(2)), 5)),
                   mk_num(1));
    c.m = a.mk_add(mp, m.mk_ite(a.mk_lt(mp, mk_num(10)), mk_num(3), mk_num(-9)));
    c.y = a.mk_add(y1, m.mk_ite(a.mk_le(c.m, mk_num(2)), mk_num(1), mk_num(0)));
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

expr_ref date_util::mk_year_of_epoch(expr* z) {
    civil_expr c(m);
    mk_civil_of_epoch(z, c);
    return c.y;
}

expr_ref date_util::mk_month_of_epoch(expr* z) {
    civil_expr c(m);
    mk_civil_of_epoch(z, c);
    return c.m;
}

expr_ref date_util::mk_day_of_epoch(expr* z) {
    civil_expr c(m);
    mk_civil_of_epoch(z, c);
    return c.d;
}

expr_ref date_util::mk_civil_roundtrip(expr* z) {
    civil_expr c(m);
    mk_civil_of_epoch(z, c);
    return mk_days_from_civil(c.y, c.m, c.d);
}

expr_ref date_util::mk_epoch_of_add(expr* z, expr* py, expr* pm, expr* pd) {
    arith_util& a = m_arith;
    civil_expr c(m);
    mk_civil_of_epoch(z, c);
    expr_ref months(a.mk_mul(mk_num(12), a.mk_add(c.y, py)), m);
    expr_ref neg1 = mk_num(-1);
    expr* mo_args[4] = { months, c.m, neg1, pm };
    expr_ref mo_total(a.mk_add(4, mo_args), m);
    expr_ref yy = mk_idiv(mo_total, 12);
    expr_ref mm(a.mk_add(mk_imod(mo_total, 12), mk_num(1)), m);
    expr_ref len = mk_days_in_month(yy, mm);
    expr_ref dd(m.mk_ite(a.mk_le(c.d, len), c.d, len), m);
    return expr_ref(a.mk_add(mk_days_from_civil(yy, mm, dd), pd), m);
}
