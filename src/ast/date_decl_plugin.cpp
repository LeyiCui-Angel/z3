/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declaration plugin for the theory of calendar dates.

Author:

    Date theory extension 2026-07-05

--*/
#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"

void date_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_date = m->mk_sort(symbol(date_sort_name()), sort_info(m_family_id, DATE_SORT));
    m->inc_ref(m_date);
    family_id aid = m->mk_family_id("arith");
    if (!m->get_plugin(aid))
        m->register_plugin(symbol("arith"), alloc(arith_decl_plugin));
    m_int = arith_util(*m).mk_int();
    m->inc_ref(m_int);
}

void date_decl_plugin::finalize() {
    if (m_date) m_manager->dec_ref(m_date);
    if (m_int)  m_manager->dec_ref(m_int);
    m_date = nullptr;
    m_int = nullptr;
}

sort* date_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) {
    if (k != DATE_SORT || num_parameters != 0) {
        m_manager->raise_exception("unexpected date sort");
        return nullptr;
    }
    return m_date;
}

func_decl* date_decl_plugin::mk_decl(decl_kind k, unsigned arity, sort* const* domain) {
    sort* i = m_int;
    sort* d = m_date;
    sort* b = m_manager->mk_bool_sort();
    symbol name;
    sort* range = nullptr;
    sort* expected[4] = { nullptr, nullptr, nullptr, nullptr };
    unsigned expected_arity = 0;
    switch (k) {
    case OP_DATE_MK:
        name = symbol("date.mk");
        expected[0] = i; expected[1] = i; expected[2] = i;
        expected_arity = 3;
        range = d;
        break;
    case OP_DATE_YEAR:
    case OP_DATE_MONTH:
    case OP_DATE_DAY:
        name = (k == OP_DATE_YEAR) ? symbol("date.year") : (k == OP_DATE_MONTH) ? symbol("date.month") : symbol("date.day");
        expected[0] = d;
        expected_arity = 1;
        range = i;
        break;
    case OP_DATE_ADD:
    case OP_DATE_SUB:
        name = (k == OP_DATE_ADD) ? symbol("date.add") : symbol("date.sub");
        expected[0] = d; expected[1] = i; expected[2] = i; expected[3] = i;
        expected_arity = 4;
        range = d;
        break;
    case OP_DATE_LT:
    case OP_DATE_LE:
    case OP_DATE_GT:
    case OP_DATE_GE:
        name = (k == OP_DATE_LT) ? symbol("date.lt") : (k == OP_DATE_LE) ? symbol("date.le") :
               (k == OP_DATE_GT) ? symbol("date.gt") : symbol("date.ge");
        expected[0] = d; expected[1] = d;
        expected_arity = 2;
        range = b;
        break;
    default:
        m_manager->raise_exception("unexpected date operator");
        return nullptr;
    }
    if (arity != expected_arity) {
        m_manager->raise_exception("invalid number of arguments to date operator");
        return nullptr;
    }
    for (unsigned j = 0; j < arity; ++j) {
        if (domain[j] != expected[j]) {
            m_manager->raise_exception("invalid argument sort to date operator");
            return nullptr;
        }
    }
    return m_manager->mk_func_decl(name, arity, expected, range, func_decl_info(m_family_id, k));
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                          unsigned arity, sort* const* domain, sort* range) {
    if (num_parameters != 0) {
        m_manager->raise_exception("date operators take no parameters");
        return nullptr;
    }
    return mk_decl(k, arity, domain);
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
    sort_names.push_back(builtin_name(date_sort_name(), DATE_SORT));
}

bool date_decl_plugin::is_value(app* e) const {
    if (!is_app_of(e, m_family_id, OP_DATE_MK))
        return false;
    date_util u(*m_manager);
    rational y, mo, d;
    return u.is_date_value(e, y, mo, d);
}

bool date_decl_plugin::is_unique_value(app* e) const {
    // distinct calendar-valid numeral triples denote distinct dates
    return is_value(e);
}

expr* date_decl_plugin::get_some_value(sort* s) {
    SASSERT(s == m_date);
    date_util u(*m_manager);
    return u.mk_date_value(rational(1), rational(1), rational(1));
}

// ----------------------------------------------------------------------
// date_util

date_util::date_util(ast_manager& m):
    m(m),
    m_fid(m.mk_family_id("date")),
    m_arith(m) {
    m_plugin = static_cast<date_decl_plugin*>(m.get_plugin(m_fid));
}

app* date_util::mk_date_value(rational const& y, rational const& mo, rational const& d) {
    return mk_mk(m_arith.mk_int(y), m_arith.mk_int(mo), m_arith.mk_int(d));
}

bool date_util::is_date_numeral(expr* e, rational& y, rational& mo, rational& d) const {
    expr* a1 = nullptr, *a2 = nullptr, *a3 = nullptr;
    return
        is_mk(e, a1, a2, a3) &&
        m_arith.is_numeral(a1, y) && y.is_int() &&
        m_arith.is_numeral(a2, mo) && mo.is_int() &&
        m_arith.is_numeral(a3, d) && d.is_int();
}

bool date_util::is_date_value(expr* e, rational& y, rational& mo, rational& d) const {
    return is_date_numeral(e, y, mo, d) && is_valid_date(y, mo, d);
}

bool date_util::is_leap_year(rational const& y) {
    return
        (mod(y, rational(4)).is_zero() && !mod(y, rational(100)).is_zero()) ||
        mod(y, rational(400)).is_zero();
}

rational date_util::days_in_month(rational const& y, rational const& mo) {
    SASSERT(rational(1) <= mo && mo <= rational(12));
    if (mo == rational(2))
        return rational(is_leap_year(y) ? 29 : 28);
    unsigned m_val = mo.get_unsigned();
    switch (m_val) {
    case 4: case 6: case 9: case 11:
        return rational(30);
    default:
        return rational(31);
    }
}

bool date_util::is_valid_date(rational const& y, rational const& mo, rational const& d) {
    if (mo < rational(1) || mo > rational(12))
        return false;
    return rational(1) <= d && d <= days_in_month(y, mo);
}

rational date_util::days_from_civil(rational const& y, rational const& mo, rational const& d) {
    // Howard Hinnant's days_from_civil generalized to unbounded integers.
    // The divisions below are Euclidean with positive divisors, i.e. floor.
    SASSERT(is_valid_date(y, mo, d));
    rational yp   = mo <= rational(2) ? y - rational(1) : y;
    rational era  = div(yp, rational(400));
    rational yoe  = yp - era * rational(400);                        // [0, 399]
    rational mp   = mod(mo + rational(9), rational(12));             // [0, 11]
    rational doy  = div(rational(153) * mp + rational(2), rational(5)) + d - rational(1);
    rational doe  = yoe * rational(365) + div(yoe, rational(4)) - div(yoe, rational(100)) + doy;
    return era * rational(146097) + doe - rational(719468);
}

void date_util::civil_from_days(rational const& n, rational& y, rational& mo, rational& d) {
    rational z    = n + rational(719468);
    rational era  = div(z, rational(146097));
    rational doe  = z - era * rational(146097);                      // [0, 146096]
    rational yoe  = div(doe - div(doe, rational(1460)) + div(doe, rational(36524)) - div(doe, rational(146096)), rational(365));
    rational yp   = yoe + era * rational(400);
    rational doy  = doe - (rational(365) * yoe + div(yoe, rational(4)) - div(yoe, rational(100)));
    rational mp   = div(rational(5) * doy + rational(2), rational(153));
    d  = doy - div(rational(153) * mp + rational(2), rational(5)) + rational(1);
    mo = mp < rational(10) ? mp + rational(3) : mp - rational(9);
    y  = mo <= rational(2) ? yp + rational(1) : yp;
    SASSERT(is_valid_date(y, mo, d));
    SASSERT(days_from_civil(y, mo, d) == n);
}

void date_util::add_period(rational& y, rational& mo, rational& d,
                           rational const& py, rational const& pm, rational const& pd) {
    SASSERT(is_valid_date(y, mo, d));
    // Step 1 -- month normalization
    rational t = mo + rational(12) * py + pm - rational(1);
    rational oy = y + div(t, rational(12));
    rational om = mod(t, rational(12)) + rational(1);
    // Step 2 -- end-of-month clamp
    rational dim = days_in_month(oy, om);
    rational clamp = d <= dim ? d : dim;
    // Step 3 -- day carry: adding pd days to the valid date (oy, om, clamp)
    civil_from_days(days_from_civil(oy, om, clamp) + pd, y, mo, d);
}
