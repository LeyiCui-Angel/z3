/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Native theory of calendar dates and periods for Z3.

--*/
#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"

date_decl_plugin::date_decl_plugin() {}

date_decl_plugin::~date_decl_plugin() {
    if (m_date_sort)   m_manager->dec_ref(m_date_sort);
    if (m_period_sort) m_manager->dec_ref(m_period_sort);
}

void date_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_date_sort = m->mk_sort(symbol("Date"), sort_info(m_family_id, DATE_SORT, 0, nullptr));
    m->inc_ref(m_date_sort);
    m_period_sort = m->mk_sort(symbol("Period"), sort_info(m_family_id, PERIOD_SORT, 0, nullptr));
    m->inc_ref(m_period_sort);
}

sort* date_decl_plugin::int_sort() const {
    arith_util a(*m_manager);
    return a.mk_int();
}

bool date_decl_plugin::is_int_sort(sort* s) const {
    arith_util a(*m_manager);
    return a.is_int(s);
}

sort* date_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) {
    switch (k) {
    case DATE_SORT:   return m_date_sort;
    case PERIOD_SORT: return m_period_sort;
    default: UNREACHABLE(); return nullptr;
    }
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                           unsigned arity, sort* const* domain, sort* range) {
    ast_manager& m = *m_manager;
    sort* isort = int_sort();
    sort* bsort = m.mk_bool_sort();
    std::stringstream msg;

    switch (k) {
    case OP_DATE_MK:
        if (arity != 3)
            msg << "date.mk expects 3 arguments, received " << arity;
        else if (!is_int_sort(domain[0]) || !is_int_sort(domain[1]) || !is_int_sort(domain[2]))
            msg << "date.mk expects Int arguments";
        else
            return m.mk_func_decl(symbol("date.mk"), arity, domain, m_date_sort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_DATE_YEAR:
        if (arity != 1)
            msg << "date.year expects 1 argument, received " << arity;
        else if (domain[0] != m_date_sort)
            msg << "date.year expects Date argument, got " << mk_pp(domain[0], m);
        else
            return m.mk_func_decl(symbol("date.year"), arity, domain, isort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_DATE_MONTH:
        if (arity != 1)
            msg << "date.month expects 1 argument, received " << arity;
        else if (domain[0] != m_date_sort)
            msg << "date.month expects Date argument, got " << mk_pp(domain[0], m);
        else
            return m.mk_func_decl(symbol("date.month"), arity, domain, isort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_DATE_DAY:
        if (arity != 1)
            msg << "date.day expects 1 argument, received " << arity;
        else if (domain[0] != m_date_sort)
            msg << "date.day expects Date argument, got " << mk_pp(domain[0], m);
        else
            return m.mk_func_decl(symbol("date.day"), arity, domain, isort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_PERIOD_MK:
        if (arity != 3)
            msg << "period.mk expects 3 arguments, received " << arity;
        else if (!is_int_sort(domain[0]) || !is_int_sort(domain[1]) || !is_int_sort(domain[2]))
            msg << "period.mk expects Int arguments";
        else
            return m.mk_func_decl(symbol("period.mk"), arity, domain, m_period_sort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_PERIOD_YEARS:
        if (arity != 1)
            msg << "period.years expects 1 argument, received " << arity;
        else if (domain[0] != m_period_sort)
            msg << "period.years expects Period argument, got " << mk_pp(domain[0], m);
        else
            return m.mk_func_decl(symbol("period.years"), arity, domain, isort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_PERIOD_MONTHS:
        if (arity != 1)
            msg << "period.months expects 1 argument, received " << arity;
        else if (domain[0] != m_period_sort)
            msg << "period.months expects Period argument, got " << mk_pp(domain[0], m);
        else
            return m.mk_func_decl(symbol("period.months"), arity, domain, isort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_PERIOD_DAYS:
        if (arity != 1)
            msg << "period.days expects 1 argument, received " << arity;
        else if (domain[0] != m_period_sort)
            msg << "period.days expects Period argument, got " << mk_pp(domain[0], m);
        else
            return m.mk_func_decl(symbol("period.days"), arity, domain, isort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_DATE_ADD:
        if (arity != 2)
            msg << "date.add expects 2 arguments, received " << arity;
        else if (domain[0] != m_date_sort)
            msg << "date.add expects Date as first argument, got " << mk_pp(domain[0], m);
        else if (domain[1] != m_period_sort)
            msg << "date.add expects Period as second argument, got " << mk_pp(domain[1], m);
        else
            return m.mk_func_decl(symbol("date.add"), arity, domain, m_date_sort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_DATE_SUB:
        if (arity != 2)
            msg << "date.sub expects 2 arguments, received " << arity;
        else if (domain[0] != m_date_sort)
            msg << "date.sub expects Date as first argument, got " << mk_pp(domain[0], m);
        else if (domain[1] != m_period_sort)
            msg << "date.sub expects Period as second argument, got " << mk_pp(domain[1], m);
        else
            return m.mk_func_decl(symbol("date.sub"), arity, domain, m_date_sort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_DATE_LT:
        if (arity != 2)
            msg << "date.lt expects 2 arguments, received " << arity;
        else if (domain[0] != m_date_sort || domain[1] != m_date_sort)
            msg << "date.lt expects Date arguments";
        else
            return m.mk_func_decl(symbol("date.lt"), arity, domain, bsort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_DATE_LE:
        if (arity != 2)
            msg << "date.le expects 2 arguments, received " << arity;
        else if (domain[0] != m_date_sort || domain[1] != m_date_sort)
            msg << "date.le expects Date arguments";
        else
            return m.mk_func_decl(symbol("date.le"), arity, domain, bsort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_DATE_GT:
        if (arity != 2)
            msg << "date.gt expects 2 arguments, received " << arity;
        else if (domain[0] != m_date_sort || domain[1] != m_date_sort)
            msg << "date.gt expects Date arguments";
        else
            return m.mk_func_decl(symbol("date.gt"), arity, domain, bsort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_DATE_GE:
        if (arity != 2)
            msg << "date.ge expects 2 arguments, received " << arity;
        else if (domain[0] != m_date_sort || domain[1] != m_date_sort)
            msg << "date.ge expects Date arguments";
        else
            return m.mk_func_decl(symbol("date.ge"), arity, domain, bsort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_PERIOD_ADD:
        if (arity != 2)
            msg << "period.add expects 2 arguments, received " << arity;
        else if (domain[0] != m_period_sort || domain[1] != m_period_sort)
            msg << "period.add expects Period arguments, got " << mk_pp(domain[0], m) << " and " << mk_pp(domain[1], m);
        else
            return m.mk_func_decl(symbol("period.add"), arity, domain, m_period_sort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_PERIOD_SUB:
        if (arity != 2)
            msg << "period.sub expects 2 arguments, received " << arity;
        else if (domain[0] != m_period_sort || domain[1] != m_period_sort)
            msg << "period.sub expects Period arguments, got " << mk_pp(domain[0], m) << " and " << mk_pp(domain[1], m);
        else
            return m.mk_func_decl(symbol("period.sub"), arity, domain, m_period_sort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    case OP_PERIOD_MUL:
        if (arity != 2)
            msg << "period.mul expects 2 arguments, received " << arity;
        else if (domain[0] != m_period_sort)
            msg << "period.mul expects Period as first argument, got " << mk_pp(domain[0], m);
        else if (!is_int_sort(domain[1]))
            msg << "period.mul expects Int as second argument, got " << mk_pp(domain[1], m);
        else
            return m.mk_func_decl(symbol("period.mul"), arity, domain, m_period_sort,
                                  func_decl_info(m_family_id, k, 0, nullptr));
        m.raise_exception(msg.str());

    default:
        UNREACHABLE();
    }
    return nullptr;
}

void date_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const& logic) {
    // Primary names (dot-style)
    op_names.push_back(builtin_name("date.mk",      OP_DATE_MK));
    op_names.push_back(builtin_name("period.mk",    OP_PERIOD_MK));
    op_names.push_back(builtin_name("date.year",    OP_DATE_YEAR));
    op_names.push_back(builtin_name("date.month",   OP_DATE_MONTH));
    op_names.push_back(builtin_name("date.day",     OP_DATE_DAY));
    op_names.push_back(builtin_name("period.years",  OP_PERIOD_YEARS));
    op_names.push_back(builtin_name("period.months", OP_PERIOD_MONTHS));
    op_names.push_back(builtin_name("period.days",   OP_PERIOD_DAYS));
    // Date arithmetic
    op_names.push_back(builtin_name("date.add",    OP_DATE_ADD));
    op_names.push_back(builtin_name("+d",          OP_DATE_ADD));
    op_names.push_back(builtin_name("date.sub",    OP_DATE_SUB));
    op_names.push_back(builtin_name("-d",          OP_DATE_SUB));
    // Date comparisons
    op_names.push_back(builtin_name("date.lt",     OP_DATE_LT));
    op_names.push_back(builtin_name("date.le",     OP_DATE_LE));
    op_names.push_back(builtin_name("date.gt",     OP_DATE_GT));
    op_names.push_back(builtin_name("date.ge",     OP_DATE_GE));
    // Period arithmetic
    op_names.push_back(builtin_name("period.add",  OP_PERIOD_ADD));
    op_names.push_back(builtin_name("+p",          OP_PERIOD_ADD));
    op_names.push_back(builtin_name("period.sub",  OP_PERIOD_SUB));
    op_names.push_back(builtin_name("-p",          OP_PERIOD_SUB));
    op_names.push_back(builtin_name("period.mul",  OP_PERIOD_MUL));
    op_names.push_back(builtin_name("*p",          OP_PERIOD_MUL));
}

void date_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) {
    sort_names.push_back(builtin_name("Date",   DATE_SORT));
    sort_names.push_back(builtin_name("Period", PERIOD_SORT));
}

bool date_decl_plugin::is_value(app* e) const {
    // mk-date with all numeral arguments is a value
    if (is_app_of(e, m_family_id, OP_DATE_MK) && e->get_num_args() == 3) {
        arith_util a(*m_manager);
        return a.is_numeral(e->get_arg(0)) && a.is_numeral(e->get_arg(1)) && a.is_numeral(e->get_arg(2));
    }
    // mk-period with all numeral arguments is a value
    if (is_app_of(e, m_family_id, OP_PERIOD_MK) && e->get_num_args() == 3) {
        arith_util a(*m_manager);
        return a.is_numeral(e->get_arg(0)) && a.is_numeral(e->get_arg(1)) && a.is_numeral(e->get_arg(2));
    }
    return false;
}

bool date_decl_plugin::is_unique_value(app* e) const {
    return is_value(e);
}

bool date_decl_plugin::are_equal(app* a, app* b) const {
    if (a == b) return true;
    if (!is_value(a) || !is_value(b)) return false;
    if (a->get_decl()->get_decl_kind() != b->get_decl()->get_decl_kind()) return false;
    // Both are ground mk-date or mk-period with numeral args; compare component-wise
    arith_util arith(*m_manager);
    rational v1, v2;
    for (unsigned i = 0; i < 3; ++i) {
        if (!arith.is_numeral(a->get_arg(i), v1) || !arith.is_numeral(b->get_arg(i), v2))
            return false;
        if (v1 != v2) return false;
    }
    return true;
}

bool date_decl_plugin::are_distinct(app* a, app* b) const {
    if (a == b) return false;
    if (!is_value(a) || !is_value(b)) return false;
    if (a->get_decl()->get_decl_kind() != b->get_decl()->get_decl_kind()) return false;
    arith_util arith(*m_manager);
    rational v1, v2;
    for (unsigned i = 0; i < 3; ++i) {
        if (!arith.is_numeral(a->get_arg(i), v1) || !arith.is_numeral(b->get_arg(i), v2))
            return false;
        if (v1 != v2) return true;
    }
    return false;
}

expr* date_decl_plugin::get_some_value(sort* s) {
    ast_manager& m = *m_manager;
    arith_util a(m);
    if (s == m_date_sort) {
        // Return mk-date(2000, 1, 1)
        expr* args[3] = { a.mk_numeral(rational(2000), true),
                          a.mk_numeral(rational(1), true),
                          a.mk_numeral(rational(1), true) };
        sort* domain[3] = { a.mk_int(), a.mk_int(), a.mk_int() };
        func_decl* fd = m.mk_func_decl(symbol("date.mk"), 3, domain, m_date_sort,
                                        func_decl_info(m_family_id, OP_DATE_MK, 0, nullptr));
        return m.mk_app(fd, 3, args);
    }
    if (s == m_period_sort) {
        // Return mk-period(0, 0, 0)
        expr* args[3] = { a.mk_numeral(rational(0), true),
                          a.mk_numeral(rational(0), true),
                          a.mk_numeral(rational(0), true) };
        sort* domain[3] = { a.mk_int(), a.mk_int(), a.mk_int() };
        func_decl* fd = m.mk_func_decl(symbol("period.mk"), 3, domain, m_period_sort,
                                        func_decl_info(m_family_id, OP_PERIOD_MK, 0, nullptr));
        return m.mk_app(fd, 3, args);
    }
    UNREACHABLE();
    return nullptr;
}

app* date_decl_plugin::mk_default_date(ast_manager& m) const {
    return to_app(const_cast<date_decl_plugin*>(this)->get_some_value(m_date_sort));
}

app* date_decl_plugin::mk_default_period(ast_manager& m) const {
    return to_app(const_cast<date_decl_plugin*>(this)->get_some_value(m_period_sort));
}
