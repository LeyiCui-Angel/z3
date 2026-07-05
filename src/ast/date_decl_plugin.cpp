/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declaration plugin for the theory of calendar dates.

Author:

    Claude 2026-07-05

--*/
#include "ast/date_decl_plugin.h"
#include "ast/ast_pp.h"

date_decl_plugin::~date_decl_plugin() {
    if (m_manager)
        m_manager->dec_ref(m_date);
}

void date_decl_plugin::set_manager(ast_manager * m, family_id id) {
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

func_decl* date_decl_plugin::mk_decl(decl_kind k, char const* name, unsigned arity, sort* const* domain, sort* range) {
    return m_manager->mk_func_decl(symbol(name), arity, domain, range, func_decl_info(m_family_id, k));
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                          unsigned arity, sort* const* domain, sort* range) {
    ast_manager& m = *m_manager;
    arith_util a(m);
    sort* int_sort = a.mk_int();
    std::stringstream msg;
    if (num_parameters != 0) {
        msg << "no parameters expected, received " << num_parameters;
        m.raise_exception(msg.str());
        return nullptr;
    }
    auto check = [&](unsigned expected_arity, sort* const* expected_domain) {
        if (arity != expected_arity) {
            msg << "incorrect number of arguments passed. Expected " << expected_arity << ", received " << arity;
            m.raise_exception(msg.str());
        }
        for (unsigned i = 0; i < arity; ++i) {
            if (domain[i] != expected_domain[i]) {
                msg << "incorrect argument " << (i + 1) << " of type " << mk_pp(domain[i], m)
                    << ", expected " << mk_pp(expected_domain[i], m);
                m.raise_exception(msg.str());
            }
        }
    };
    sort* iii[3] = { int_sort, int_sort, int_sort };
    sort* diii[4] = { m_date, int_sort, int_sort, int_sort };
    sort* d1[1] = { m_date };
    sort* dd[2] = { m_date, m_date };
    switch (k) {
    case OP_DATE_MK:
        check(3, iii);
        return mk_decl(k, "date.mk", arity, domain, m_date);
    case OP_DATE_YEAR:
        check(1, d1);
        return mk_decl(k, "date.year", arity, domain, int_sort);
    case OP_DATE_MONTH:
        check(1, d1);
        return mk_decl(k, "date.month", arity, domain, int_sort);
    case OP_DATE_DAY:
        check(1, d1);
        return mk_decl(k, "date.day", arity, domain, int_sort);
    case OP_DATE_ADD:
        check(4, diii);
        return mk_decl(k, "date.add", arity, domain, m_date);
    case OP_DATE_SUB:
        check(4, diii);
        return mk_decl(k, "date.sub", arity, domain, m_date);
    case OP_DATE_LT:
        check(2, dd);
        return mk_decl(k, "date.lt", arity, domain, m.mk_bool_sort());
    case OP_DATE_LE:
        check(2, dd);
        return mk_decl(k, "date.le", arity, domain, m.mk_bool_sort());
    case OP_DATE_GT:
        check(2, dd);
        return mk_decl(k, "date.gt", arity, domain, m.mk_bool_sort());
    case OP_DATE_GE:
        check(2, dd);
        return mk_decl(k, "date.ge", arity, domain, m.mk_bool_sort());
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
    if (!is_app_of(e, m_family_id, OP_DATE_MK))
        return false;
    arith_util a(*m_manager);
    rational y, mo, d;
    return
        a.is_numeral(e->get_arg(0), y) &&
        a.is_numeral(e->get_arg(1), mo) &&
        a.is_numeral(e->get_arg(2), d) &&
        is_valid_date(y, mo, d);
}

bool date_decl_plugin::is_unique_value(app* e) const {
    return is_value(e);
}

expr* date_decl_plugin::get_some_value(sort* s) {
    SASSERT(s == m_date);
    arith_util a(*m_manager);
    expr* args[3] = { a.mk_int(1), a.mk_int(1), a.mk_int(1) };
    return m_manager->mk_app(m_family_id, OP_DATE_MK, 3, args);
}

bool date_decl_plugin::is_leap_year(rational const& y) {
    return (mod(y, rational(4)).is_zero() && !mod(y, rational(100)).is_zero()) || mod(y, rational(400)).is_zero();
}

rational date_decl_plugin::days_in_month(rational const& y, rational const& m) {
    SASSERT(rational(1) <= m && m <= rational(12));
    switch (m.get_unsigned()) {
    case 4: case 6: case 9: case 11:
        return rational(30);
    case 2:
        return rational(is_leap_year(y) ? 29 : 28);
    default:
        return rational(31);
    }
}

bool date_decl_plugin::is_valid_date(rational const& y, rational const& m, rational const& d) {
    return
        y.is_int() && m.is_int() && d.is_int() &&
        rational(1) <= m && m <= rational(12) &&
        rational(1) <= d && d <= days_in_month(y, m);
}

rational date_decl_plugin::rata_die(rational const& y, rational const& m, rational const& d) {
    SASSERT(is_valid_date(y, m, d));
    static const unsigned days_before[12] = { 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334 };
    rational y1 = y - 1;
    rational rd = rational(365) * y1 + div(y1, rational(4)) - div(y1, rational(100)) + div(y1, rational(400));
    rd += rational(days_before[m.get_unsigned() - 1]);
    if (m >= rational(3) && is_leap_year(y))
        rd += rational(1);
    return rd + d;
}

void date_decl_plugin::date_of_rata_die(rational const& rd, rational& y, rational& m, rational& d) {
    // Howard Hinnant's civil_from_days, shifted to Rata Die day numbers.
    rational z = rd + rational(305);                                    // days since 0000-03-01
    rational era = div(z, rational(146097));
    rational doe = z - era * rational(146097);                          // [0, 146096]
    rational yoe = div(doe - div(doe, rational(1460)) + div(doe, rational(36524)) - div(doe, rational(146096)),
                       rational(365));                                  // [0, 399]
    rational doy = doe - (rational(365) * yoe + div(yoe, rational(4)) - div(yoe, rational(100))); // [0, 365]
    rational mp = div(rational(5) * doy + rational(2), rational(153));  // [0, 11]
    d = doy - div(rational(153) * mp + rational(2), rational(5)) + rational(1);
    m = mp < rational(10) ? mp + rational(3) : mp - rational(9);
    y = yoe + era * rational(400);
    if (m <= rational(2))
        y += rational(1);
    SASSERT(is_valid_date(y, m, d));
    SASSERT(rata_die(y, m, d) == rd);
}

void date_decl_plugin::add(rational const& y, rational const& m, rational const& d,
                           rational const& py, rational const& pm, rational const& pd,
                           rational& oy, rational& om, rational& od) {
    SASSERT(is_valid_date(y, m, d));
    // Step 1 -- month normalization.
    rational t = m + rational(12) * py + pm - 1;
    oy = y + div(t, rational(12));
    om = mod(t, rational(12)) + 1;
    // Step 2 -- end-of-month clamp.
    rational cd = std::min(d, days_in_month(oy, om));
    // Step 3 -- day carry: shift the day number.
    date_of_rata_die(rata_die(oy, om, cd) + pd, oy, om, od);
}
