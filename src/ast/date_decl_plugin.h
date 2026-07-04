/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Declaration plugin for a native theory of calendar dates.

    The theory introduces a single sort

        Date

    together with a total constructor, three selectors, calendar
    arithmetic and lexicographic comparisons:

        (date.mk    Int Int Int Date)   ; year month day
        (date.year  Date Int)
        (date.month Date Int)
        (date.day   Date Int)
        (date.add   Date Int Int Int Date)  ; d py pm pd
        (date.sub   Date Int Int Int Date)  ; d py pm pd
        (date.lt    Date Date Bool)
        (date.le    Date Date Bool)
        (date.gt    Date Date Bool)
        (date.ge    Date Date Bool)

    Date values denote calendar-valid proleptic Gregorian dates.
    See Dates.smt2 for the full specification.

Author:

    Angel Cui 2026

--*/
#pragma once

#include "ast/ast.h"

enum date_sort_kind {
    DATE_SORT
};

enum date_op_kind {
    OP_DATE_MK,
    OP_DATE_YEAR,
    OP_DATE_MONTH,
    OP_DATE_DAY,
    OP_DATE_ADD,
    OP_DATE_SUB,
    OP_DATE_LT,
    OP_DATE_LE,
    OP_DATE_GT,
    OP_DATE_GE,
    LAST_DATE_OP
};

class date_decl_plugin : public decl_plugin {
    sort* m_date { nullptr };

    void set_manager(ast_manager * m, family_id id) override;

    func_decl* mk_func_decl(decl_kind k, char const* name,
                            unsigned arity, sort* const* domain, sort* range);

public:
    date_decl_plugin() {}

    ~date_decl_plugin() override {}

    void finalize() override {}

    decl_plugin* mk_fresh() override { return alloc(date_decl_plugin); }

    sort* mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override { return m_date; }

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                            unsigned arity, sort* const* domain, sort* range) override;

    void get_op_names(svector<builtin_name>& op_names, symbol const& logic) override;

    void get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) override;

    expr* get_some_value(sort* s) override;

    sort* date_sort() const { return m_date; }
};

/**
   \brief Convenience wrapper used by the theory solvers to recognize and
   construct terms of the date family.
*/
class date_util {
    ast_manager&    m;
    family_id       m_fid;
    date_decl_plugin* m_plugin { nullptr };

public:
    date_util(ast_manager& m);

    ast_manager& get_manager() const { return m; }
    family_id    get_family_id() const { return m_fid; }
    date_decl_plugin& plugin() const { return *m_plugin; }

    sort* mk_date_sort() { return m_plugin->date_sort(); }
    bool  is_date_sort(sort* s) const { return s->get_family_id() == m_fid && s->get_decl_kind() == DATE_SORT; }
    bool  is_date(expr* e) const { return is_date_sort(e->get_sort()); }

    bool is_mk(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_MK); }
    bool is_year(expr const* e)  const { return is_app_of(e, m_fid, OP_DATE_YEAR); }
    bool is_month(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_MONTH); }
    bool is_day(expr const* e)   const { return is_app_of(e, m_fid, OP_DATE_DAY); }
    bool is_add(expr const* e)   const { return is_app_of(e, m_fid, OP_DATE_ADD); }
    bool is_sub(expr const* e)   const { return is_app_of(e, m_fid, OP_DATE_SUB); }
    bool is_lt(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_LT); }
    bool is_le(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_LE); }
    bool is_gt(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_GT); }
    bool is_ge(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_GE); }

    app* mk_mk(expr* y, expr* m_, expr* d);
    app* mk_year(expr* d)  { return m.mk_app(m_fid, OP_DATE_YEAR, 1, &d); }
    app* mk_month(expr* d) { return m.mk_app(m_fid, OP_DATE_MONTH, 1, &d); }
    app* mk_day(expr* d)   { return m.mk_app(m_fid, OP_DATE_DAY, 1, &d); }
};
