/*++
Copyright (c) 2026 Theoria

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declaration plugin for the theory of calendar dates.

Author:

    Claude (Theoria date theory) 2026-07-07

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
    m_date = m->mk_sort(symbol("Date"), sort_info(m_family_id, DATE_SORT, sort_size::mk_infinite(), 0, nullptr));
    m->inc_ref(m_date);
    arith_util a(*m);
    m_int = a.mk_int();
    m->inc_ref(m_int);
}

sort * date_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    if (k != DATE_SORT || num_parameters != 0) {
        m_manager->raise_exception("unexpected date sort");
        return nullptr;
    }
    return m_date;
}

func_decl * date_decl_plugin::mk_op(char const* name, decl_kind k, unsigned arity, sort * const * domain, sort * range) {
    return m_manager->mk_func_decl(symbol(name), arity, domain, range, func_decl_info(m_family_id, k, 0, nullptr));
}

func_decl * date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                           unsigned arity, sort * const * domain, sort * range) {
    ast_manager & m = *m_manager;
    if (num_parameters != 0) {
        m.raise_exception("date operations do not take parameters");
        return nullptr;
    }
    auto check = [&](unsigned expected_arity, std::initializer_list<sort*> expected) {
        if (arity != expected_arity) {
            std::stringstream msg;
            msg << "incorrect number of arguments for date operation; expected " << expected_arity << ", got " << arity;
            m.raise_exception(msg.str());
        }
        unsigned i = 0;
        for (sort* s : expected) {
            if (domain[i] != s) {
                std::stringstream msg;
                msg << "incorrect argument sort " << mk_pp(domain[i], m) << " at position " << i
                    << " for date operation; expected " << mk_pp(s, m);
                m.raise_exception(msg.str());
            }
            ++i;
        }
    };
    switch (k) {
    case OP_DATE_MK:
        check(3, { m_int, m_int, m_int });
        return mk_op("date.mk", k, arity, domain, m_date);
    case OP_DATE_YEAR:
        check(1, { m_date });
        return mk_op("date.year", k, arity, domain, m_int);
    case OP_DATE_MONTH:
        check(1, { m_date });
        return mk_op("date.month", k, arity, domain, m_int);
    case OP_DATE_DAY:
        check(1, { m_date });
        return mk_op("date.day", k, arity, domain, m_int);
    case OP_DATE_TO_DAYS:
        check(1, { m_date });
        return mk_op("date.to_days", k, arity, domain, m_int);
    case OP_DATE_FROM_DAYS:
        check(1, { m_int });
        return mk_op("date.from_days", k, arity, domain, m_date);
    case OP_DATE_ADD_DAYS:
        check(2, { m_date, m_int });
        return mk_op("date.add_days", k, arity, domain, m_date);
    case OP_DATE_SUB:
        check(2, { m_date, m_date });
        return mk_op("date.sub", k, arity, domain, m_int);
    case OP_DATE_DOW:
        check(1, { m_date });
        return mk_op("date.dow", k, arity, domain, m_int);
    case OP_DATE_LT:
        check(2, { m_date, m_date });
        return mk_op("date.lt", k, arity, domain, m.mk_bool_sort());
    case OP_DATE_LE:
        check(2, { m_date, m_date });
        return mk_op("date.le", k, arity, domain, m.mk_bool_sort());
    case OP_DATE_VALID:
        check(3, { m_int, m_int, m_int });
        return mk_op("date.valid", k, arity, domain, m.mk_bool_sort());
    case OP_DATE_LEAP_YEAR:
        check(1, { m_int });
        return mk_op("date.leap_year", k, arity, domain, m.mk_bool_sort());
    default:
        m.raise_exception("unexpected date operation");
        return nullptr;
    }
}

void date_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    op_names.push_back(builtin_name("date.mk", OP_DATE_MK));
    op_names.push_back(builtin_name("date.year", OP_DATE_YEAR));
    op_names.push_back(builtin_name("date.month", OP_DATE_MONTH));
    op_names.push_back(builtin_name("date.day", OP_DATE_DAY));
    op_names.push_back(builtin_name("date.to_days", OP_DATE_TO_DAYS));
    op_names.push_back(builtin_name("date.from_days", OP_DATE_FROM_DAYS));
    op_names.push_back(builtin_name("date.add_days", OP_DATE_ADD_DAYS));
    op_names.push_back(builtin_name("date.sub", OP_DATE_SUB));
    op_names.push_back(builtin_name("date.dow", OP_DATE_DOW));
    op_names.push_back(builtin_name("date.lt", OP_DATE_LT));
    op_names.push_back(builtin_name("date.le", OP_DATE_LE));
    op_names.push_back(builtin_name("date.valid", OP_DATE_VALID));
    op_names.push_back(builtin_name("date.leap_year", OP_DATE_LEAP_YEAR));
}

void date_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name("Date", DATE_SORT));
}

bool date_decl_plugin::is_value(app * e) const {
    if (!is_app_of(e, m_family_id, OP_DATE_FROM_DAYS))
        return false;
    arith_util a(*m_manager);
    return a.is_numeral(e->get_arg(0));
}

bool date_decl_plugin::is_unique_value(app * e) const {
    // date.from_days is a bijection, so from_days of a numeral is a unique value.
    return is_value(e);
}

expr * date_decl_plugin::get_some_value(sort * s) {
    SASSERT(s == m_date);
    arith_util a(*m_manager);
    expr * zero = a.mk_int(0);
    return m_manager->mk_app(m_family_id, OP_DATE_FROM_DAYS, 1, &zero);
}

date_util::date_util(ast_manager & m):
    m(m),
    m_fid(m.mk_family_id("date")) {
    if (!m.has_plugin(m_fid))
        m.register_plugin(m_fid, alloc(date_decl_plugin));
    m_plugin = static_cast<date_decl_plugin*>(m.get_plugin(m_fid));
}

bool date_util::sort_contains_date(sort * s) const {
    if (s->get_family_id() == m_fid)
        return true;
    unsigned num = s->get_num_parameters();
    for (unsigned i = 0; i < num; ++i) {
        parameter const & p = s->get_parameter(i);
        if (p.is_ast() && is_sort(p.get_ast()) && sort_contains_date(to_sort(p.get_ast())))
            return true;
    }
    return false;
}
