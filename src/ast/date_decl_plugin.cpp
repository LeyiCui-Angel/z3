/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declaration plugin for the Dates theory.

Author:

    Date theory extension 2026-07-04

--*/
#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"

void date_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_date = m->mk_sort(symbol("Date"), sort_info(m_family_id, DATE_SORT, sort_size::mk_infinite()));
    m->inc_ref(m_date);
    arith_util a(*m);
    m_int = a.mk_int();
    m->inc_ref(m_int);
}

void date_decl_plugin::finalize() {
    if (m_date) m_manager->dec_ref(m_date);
    if (m_int) m_manager->dec_ref(m_int);
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

func_decl* date_decl_plugin::mk_date_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, char const* name) {
    return m_manager->mk_func_decl(symbol(name), arity, domain, range, func_decl_info(m_family_id, k, 0, nullptr));
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                          unsigned arity, sort* const* domain, sort* range) {
    ast_manager& m = *m_manager;
    std::stringstream msg;
    if (num_parameters != 0) {
        msg << "date operations do not take parameters";
        m.raise_exception(msg.str());
        return nullptr;
    }
    auto check = [&](unsigned expected_arity, std::initializer_list<sort*> expected) {
        if (arity != expected_arity) {
            msg << "incorrect number of arguments. Expected " << expected_arity << ", received " << arity;
            m.raise_exception(msg.str());
        }
        unsigned i = 0;
        for (sort* s : expected) {
            if (domain[i] != s) {
                msg << "incorrect argument " << (i + 1) << " of sort " << mk_pp(domain[i], m)
                    << ", expected " << mk_pp(s, m);
                m.raise_exception(msg.str());
            }
            ++i;
        }
    };
    switch (k) {
    case OP_DATE_MK:
        check(3, { m_int, m_int, m_int });
        return mk_date_fun(k, arity, domain, m_date, "date.mk");
    case OP_DATE_YEAR:
        check(1, { m_date });
        return mk_date_fun(k, arity, domain, m_int, "date.year");
    case OP_DATE_MONTH:
        check(1, { m_date });
        return mk_date_fun(k, arity, domain, m_int, "date.month");
    case OP_DATE_DAY:
        check(1, { m_date });
        return mk_date_fun(k, arity, domain, m_int, "date.day");
    case OP_DATE_ADD:
        check(4, { m_date, m_int, m_int, m_int });
        return mk_date_fun(k, arity, domain, m_date, "date.add");
    case OP_DATE_SUB:
        check(4, { m_date, m_int, m_int, m_int });
        return mk_date_fun(k, arity, domain, m_date, "date.sub");
    case OP_DATE_LT:
        check(2, { m_date, m_date });
        return mk_date_fun(k, arity, domain, m.mk_bool_sort(), "date.lt");
    case OP_DATE_LE:
        check(2, { m_date, m_date });
        return mk_date_fun(k, arity, domain, m.mk_bool_sort(), "date.le");
    case OP_DATE_GT:
        check(2, { m_date, m_date });
        return mk_date_fun(k, arity, domain, m.mk_bool_sort(), "date.gt");
    case OP_DATE_GE:
        check(2, { m_date, m_date });
        return mk_date_fun(k, arity, domain, m.mk_bool_sort(), "date.ge");
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
    if (!a.is_numeral(e->get_arg(0), y) ||
        !a.is_numeral(e->get_arg(1), mo) ||
        !a.is_numeral(e->get_arg(2), d))
        return false;
    return date_util::is_valid_date(y, mo, d);
}

bool date_decl_plugin::is_unique_value(app* e) const {
    // date.mk is injective on calendar-valid numeral triples.
    return is_value(e);
}

expr* date_decl_plugin::get_some_value(sort* s) {
    SASSERT(s == m_date);
    arith_util a(*m_manager);
    expr* args[3] = { a.mk_int(1), a.mk_int(1), a.mk_int(1) };
    return m_manager->mk_app(m_family_id, OP_DATE_MK, 3, args);
}

date_util::date_util(ast_manager& m):
    m(m),
    m_fid(m.mk_family_id("date")),
    m_arith(m) {
    m_plugin = static_cast<date_decl_plugin*>(m.get_plugin(m_fid));
}

bool date_util::is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d) const {
    if (!is_mk(e))
        return false;
    app const* a = to_app(e);
    return
        m_arith.is_numeral(a->get_arg(0), y) &&
        m_arith.is_numeral(a->get_arg(1), mo) &&
        m_arith.is_numeral(a->get_arg(2), d);
}

bool date_util::is_leap_year(rational const& y) {
    return (mod(y, rational(4)).is_zero() && !mod(y, rational(100)).is_zero()) ||
           mod(y, rational(400)).is_zero();
}

rational date_util::days_in_month(rational const& y, rational const& mo) {
    if (mo == rational(2))
        return is_leap_year(y) ? rational(29) : rational(28);
    if (mo == rational(4) || mo == rational(6) || mo == rational(9) || mo == rational(11))
        return rational(30);
    return rational(31);
}

bool date_util::is_valid_date(rational const& y, rational const& mo, rational const& d) {
    if (!y.is_int() || !mo.is_int() || !d.is_int())
        return false;
    if (mo < rational(1) || mo > rational(12))
        return false;
    return d >= rational(1) && d <= days_in_month(y, mo);
}
