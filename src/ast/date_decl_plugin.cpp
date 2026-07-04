/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declaration plugin for a native theory of calendar dates.
    See date_decl_plugin.h and Dates.smt2 for the specification.

Author:

    Angel Cui 2026

--*/
#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include <sstream>

void date_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_date = m->mk_sort(symbol("Date"), sort_info(m_family_id, DATE_SORT, 0, nullptr));
    m->inc_ref(m_date);
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, char const* name,
                                          unsigned arity, sort* const* domain, sort* range) {
    ast_manager& m = *m_manager;
    return m.mk_func_decl(symbol(name), arity, domain, range,
                          func_decl_info(m_family_id, k));
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                          unsigned arity, sort* const* domain, sort* range) {
    ast_manager& m = *m_manager;
    arith_util a(m);
    sort* i = a.mk_int();
    sort* b = m.mk_bool_sort();
    sort* dt = m_date;
    std::stringstream msg;

    auto check_dom = [&](unsigned expected) -> bool {
        if (arity != expected) {
            msg << "date operator expects " << expected << " arguments, got " << arity;
            return false;
        }
        return true;
    };

    switch (k) {
    case OP_DATE_MK: {
        if (!check_dom(3)) break;
        sort* dom[3] = { i, i, i };
        return mk_func_decl(k, "date.mk", 3, dom, dt);
    }
    case OP_DATE_YEAR:
        if (!check_dom(1)) break;
        return mk_func_decl(k, "date.year", 1, &dt, i);
    case OP_DATE_MONTH:
        if (!check_dom(1)) break;
        return mk_func_decl(k, "date.month", 1, &dt, i);
    case OP_DATE_DAY:
        if (!check_dom(1)) break;
        return mk_func_decl(k, "date.day", 1, &dt, i);
    case OP_DATE_ADD: {
        if (!check_dom(4)) break;
        sort* dom[4] = { dt, i, i, i };
        return mk_func_decl(k, "date.add", 4, dom, dt);
    }
    case OP_DATE_SUB: {
        if (!check_dom(4)) break;
        sort* dom[4] = { dt, i, i, i };
        return mk_func_decl(k, "date.sub", 4, dom, dt);
    }
    case OP_DATE_LT: {
        if (!check_dom(2)) break;
        sort* dom[2] = { dt, dt };
        return mk_func_decl(k, "date.lt", 2, dom, b);
    }
    case OP_DATE_LE: {
        if (!check_dom(2)) break;
        sort* dom[2] = { dt, dt };
        return mk_func_decl(k, "date.le", 2, dom, b);
    }
    case OP_DATE_GT: {
        if (!check_dom(2)) break;
        sort* dom[2] = { dt, dt };
        return mk_func_decl(k, "date.gt", 2, dom, b);
    }
    case OP_DATE_GE: {
        if (!check_dom(2)) break;
        sort* dom[2] = { dt, dt };
        return mk_func_decl(k, "date.ge", 2, dom, b);
    }
    default:
        UNREACHABLE();
        return nullptr;
    }
    m.raise_exception(msg.str());
    return nullptr;
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
}

void date_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) {
    sort_names.push_back(builtin_name("Date", DATE_SORT));
}

expr* date_decl_plugin::get_some_value(sort* s) {
    ast_manager& m = *m_manager;
    arith_util a(m);
    expr* args[3] = { a.mk_int(2000), a.mk_int(1), a.mk_int(1) };
    return m.mk_app(m_family_id, OP_DATE_MK, 3, args);
}

date_util::date_util(ast_manager& m):
    m(m),
    m_fid(m.mk_family_id("date")) {
    m_plugin = static_cast<date_decl_plugin*>(m.get_plugin(m_fid));
}

app* date_util::mk_mk(expr* y, expr* mo, expr* d) {
    expr* args[3] = { y, mo, d };
    return m.mk_app(m_fid, OP_DATE_MK, 3, args);
}
