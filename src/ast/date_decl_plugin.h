/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Declaration plugin for the Dates theory.

    The theory introduces a single interpreted sort Date whose values
    denote calendar-valid dates in the proleptic Gregorian calendar,
    together with the constructor date.mk, the selectors date.year,
    date.month, date.day, the period arithmetic operations date.add and
    date.sub, and the chronological comparisons date.lt, date.le,
    date.gt, date.ge.

Author:

    Date theory extension 2026-07-04

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"

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
    OP_DATE_GE
};

class date_decl_plugin : public decl_plugin {
    sort* m_date { nullptr };
    sort* m_int { nullptr };

    void set_manager(ast_manager * m, family_id id) override;

    func_decl* mk_date_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, char const* name);

public:
    date_decl_plugin() {}

    ~date_decl_plugin() override {}

    void finalize() override;

    decl_plugin* mk_fresh() override { return alloc(date_decl_plugin); }

    sort* mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override;

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
        unsigned arity, sort* const* domain, sort* range) override;

    void get_op_names(svector<builtin_name>& op_names, symbol const& logic) override;

    void get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) override;

    bool is_value(app* e) const override;

    bool is_unique_value(app* e) const override;

    expr* get_some_value(sort* s) override;

    sort* date_sort() const { return m_date; }
};

class date_util {
    ast_manager&      m;
    date_decl_plugin* m_plugin;
    family_id         m_fid;
    arith_util        m_arith;

public:
    date_util(ast_manager& m);

    ast_manager& get_manager() const { return m; }

    family_id get_family_id() const { return m_fid; }

    date_decl_plugin& plugin() const { return *m_plugin; }

    sort* mk_date_sort() const { return m_plugin->date_sort(); }

    bool is_date(sort* s) const { return is_sort_of(s, m_fid, DATE_SORT); }

    bool is_date(expr* e) const { return is_date(e->get_sort()); }

    app* mk_mk(expr* y, expr* mo, expr* d) {
        expr* args[3] = { y, mo, d };
        return m.mk_app(m_fid, OP_DATE_MK, 3, args);
    }

    app* mk_mk(rational const& y, rational const& mo, rational const& d) {
        return mk_mk(m_arith.mk_int(y), m_arith.mk_int(mo), m_arith.mk_int(d));
    }

    app* mk_year(expr* d) { return m.mk_app(m_fid, OP_DATE_YEAR, d); }
    app* mk_month(expr* d) { return m.mk_app(m_fid, OP_DATE_MONTH, d); }
    app* mk_day(expr* d) { return m.mk_app(m_fid, OP_DATE_DAY, d); }

    app* mk_add(expr* d, expr* py, expr* pm, expr* pd) {
        expr* args[4] = { d, py, pm, pd };
        return m.mk_app(m_fid, OP_DATE_ADD, 4, args);
    }

    app* mk_sub(expr* d, expr* py, expr* pm, expr* pd) {
        expr* args[4] = { d, py, pm, pd };
        return m.mk_app(m_fid, OP_DATE_SUB, 4, args);
    }

    app* mk_lt(expr* d1, expr* d2) { return m.mk_app(m_fid, OP_DATE_LT, d1, d2); }
    app* mk_le(expr* d1, expr* d2) { return m.mk_app(m_fid, OP_DATE_LE, d1, d2); }
    app* mk_gt(expr* d1, expr* d2) { return m.mk_app(m_fid, OP_DATE_GT, d1, d2); }
    app* mk_ge(expr* d1, expr* d2) { return m.mk_app(m_fid, OP_DATE_GE, d1, d2); }

    bool is_mk(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_MK); }
    bool is_year(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_YEAR); }
    bool is_month(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_MONTH); }
    bool is_day(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_DAY); }
    bool is_add(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_ADD); }
    bool is_sub(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_SUB); }
    bool is_lt(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_LT); }
    bool is_le(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_LE); }
    bool is_gt(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_GT); }
    bool is_ge(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_GE); }

    bool is_selector(expr const* e) const { return is_year(e) || is_month(e) || is_day(e); }
    bool is_comparison(expr const* e) const { return is_lt(e) || is_le(e) || is_gt(e) || is_ge(e); }

    // recognize (date.mk n1 n2 n3) with integer numeral arguments
    bool is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d) const;

    // calendar helpers over concrete numbers
    static bool is_leap_year(rational const& y);
    static rational days_in_month(rational const& y, rational const& mo);
    static bool is_valid_date(rational const& y, rational const& mo, rational const& d);
};
