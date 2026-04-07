/*++
Copyright (c) 2026 CMU PASTA Lab

Module Name:

    date_decl_plugin.cpp

Abstract:

    Implementation of the Date theory declaration plugin.

Author:

    Angel Cui

--*/

#include "ast/date_decl_plugin.h"

// ============================================================
// date_decl_plugin
// ============================================================

date_decl_plugin::~date_decl_plugin() {
}

void date_decl_plugin::finalize() {
    if (m_date_sort) {
        m_manager->dec_ref(m_date_sort);
        m_date_sort = nullptr;
    }
}

void date_decl_plugin::set_manager(ast_manager* m, family_id id) {
    decl_plugin::set_manager(m, id);
}

sort* date_decl_plugin::mk_sort(decl_kind k, unsigned num_params, parameter const* params) {
    if (k != DATE_SORT) {
        m_manager->raise_exception("date theory: unknown sort kind");
        return nullptr;
    }
    if (!m_date_sort) {
        sort_info info(m_family_id, DATE_SORT);
        m_date_sort = m_manager->mk_sort(symbol("Date"), info);
        m_manager->inc_ref(m_date_sort);
    }
    return m_date_sort;
}

func_decl* date_decl_plugin::mk_func_decl(
    decl_kind k, unsigned num_params, parameter const* params,
    unsigned arity, sort* const* domain, sort* range)
{
    // Ensure Date sort exists
    if (!m_date_sort)
        mk_sort(DATE_SORT, 0, nullptr);

    sort* date_sort = m_date_sort;
    sort* int_sort  = arith_util(*m_manager).mk_int();
    sort* bool_sort = m_manager->mk_bool_sort();

    func_decl_info info(m_family_id, k);

    switch (k) {
    case OP_DATE_MK: {
        sort* dom[3] = { int_sort, int_sort, int_sort };
        return m_manager->mk_func_decl(symbol("date.mk"), 3, dom, date_sort, info);
    }
    case OP_DATE_YEAR: {
        sort* dom[1] = { date_sort };
        return m_manager->mk_func_decl(symbol("date.year"), 1, dom, int_sort, info);
    }
    case OP_DATE_MONTH: {
        sort* dom[1] = { date_sort };
        return m_manager->mk_func_decl(symbol("date.month"), 1, dom, int_sort, info);
    }
    case OP_DATE_DAY: {
        sort* dom[1] = { date_sort };
        return m_manager->mk_func_decl(symbol("date.day"), 1, dom, int_sort, info);
    }
    case OP_DATE_ADD: {
        sort* dom[4] = { date_sort, int_sort, int_sort, int_sort };
        return m_manager->mk_func_decl(symbol("date.add"), 4, dom, date_sort, info);
    }
    case OP_DATE_SUB: {
        sort* dom[4] = { date_sort, int_sort, int_sort, int_sort };
        return m_manager->mk_func_decl(symbol("date.sub"), 4, dom, date_sort, info);
    }
    case OP_DATE_LT: {
        sort* dom[2] = { date_sort, date_sort };
        return m_manager->mk_func_decl(symbol("date.lt"), 2, dom, bool_sort, info);
    }
    case OP_DATE_LE: {
        sort* dom[2] = { date_sort, date_sort };
        return m_manager->mk_func_decl(symbol("date.le"), 2, dom, bool_sort, info);
    }
    case OP_DATE_GT: {
        sort* dom[2] = { date_sort, date_sort };
        return m_manager->mk_func_decl(symbol("date.gt"), 2, dom, bool_sort, info);
    }
    case OP_DATE_GE: {
        sort* dom[2] = { date_sort, date_sort };
        return m_manager->mk_func_decl(symbol("date.ge"), 2, dom, bool_sort, info);
    }
    default:
        m_manager->raise_exception("date theory: unknown function kind");
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
}

void date_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) {
    sort_names.push_back(builtin_name("Date", DATE_SORT));
}

expr* date_decl_plugin::get_some_value(sort* s) {
    if (!m_date_sort)
        mk_sort(DATE_SORT, 0, nullptr);
    if (s != m_date_sort)
        return nullptr;
    // Return date.mk(0, 1, 1) as a default canonical value
    arith_util autil(*m_manager);
    app* zero = autil.mk_int(0);
    app* one  = autil.mk_int(1);
    sort* int_sort = autil.mk_int();
    sort* dom[3] = { int_sort, int_sort, int_sort };
    func_decl_info info(m_family_id, OP_DATE_MK);
    func_decl* mk_decl = m_manager->mk_func_decl(symbol("date.mk"), 3, dom, m_date_sort, info);
    expr* args[3] = { zero, one, one };
    return m_manager->mk_app(mk_decl, 3, args);
}

// ============================================================
// date_util
// ============================================================

family_id date_util::fid() const {
    if (m_fid == null_family_id)
        m_fid = m.get_family_id("date");
    return m_fid;
}

sort* date_util::get_date_sort() const {
    return m.mk_sort(fid(), DATE_SORT, 0, nullptr);
}

bool date_util::is_date(sort const* s) const {
    return s->get_family_id() == fid() && s->get_decl_kind() == DATE_SORT;
}

bool date_util::is_date(expr const* e) const {
    return is_app(e) && is_date(to_app(e)->get_sort());
}

app* date_util::mk_date(expr* y, expr* mo, expr* d) {
    expr* args[3] = { y, mo, d };
    return m.mk_app(fid(), OP_DATE_MK, 0, nullptr, 3, args);
}

app* date_util::mk_year(expr* d) {
    return m.mk_app(fid(), OP_DATE_YEAR, 0, nullptr, 1, &d);
}

app* date_util::mk_month(expr* d) {
    return m.mk_app(fid(), OP_DATE_MONTH, 0, nullptr, 1, &d);
}

app* date_util::mk_day(expr* d) {
    return m.mk_app(fid(), OP_DATE_DAY, 0, nullptr, 1, &d);
}

app* date_util::mk_add(expr* d, expr* py, expr* pm, expr* pd) {
    expr* args[4] = { d, py, pm, pd };
    return m.mk_app(fid(), OP_DATE_ADD, 0, nullptr, 4, args);
}

app* date_util::mk_sub(expr* d, expr* py, expr* pm, expr* pd) {
    expr* args[4] = { d, py, pm, pd };
    return m.mk_app(fid(), OP_DATE_SUB, 0, nullptr, 4, args);
}

app* date_util::mk_lt(expr* d1, expr* d2) {
    expr* args[2] = { d1, d2 };
    return m.mk_app(fid(), OP_DATE_LT, 0, nullptr, 2, args);
}

app* date_util::mk_le(expr* d1, expr* d2) {
    expr* args[2] = { d1, d2 };
    return m.mk_app(fid(), OP_DATE_LE, 0, nullptr, 2, args);
}

app* date_util::mk_gt(expr* d1, expr* d2) {
    expr* args[2] = { d1, d2 };
    return m.mk_app(fid(), OP_DATE_GT, 0, nullptr, 2, args);
}

app* date_util::mk_ge(expr* d1, expr* d2) {
    expr* args[2] = { d1, d2 };
    return m.mk_app(fid(), OP_DATE_GE, 0, nullptr, 2, args);
}
