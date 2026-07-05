/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Declaration plugin for the theory of calendar dates.

    The theory introduces the sort Date together with a constructor
    date.mk : Int Int Int -> Date, selectors date.year, date.month,
    date.day, calendar arithmetic date.add, date.sub, and the
    lexicographic comparisons date.lt, date.le, date.gt, date.ge.

    Date values denote calendar-valid dates in the proleptic Gregorian
    calendar with unbounded integer years. Applications of date.mk to
    triples that are not calendar-valid are well-sorted, but their
    meaning is intentionally unspecified.

Author:

    Claude 2026-07-05

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

    void set_manager(ast_manager * m, family_id id) override;

    func_decl* mk_decl(decl_kind k, char const* name, unsigned arity, sort* const* domain, sort* range);

public:
    date_decl_plugin() = default;

    ~date_decl_plugin() override;

    void finalize() override {}

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

    // Calendar helpers shared by the rewriter and the theory solvers.

    static bool is_leap_year(rational const& y);

    static rational days_in_month(rational const& y, rational const& m);

    static bool is_valid_date(rational const& y, rational const& m, rational const& d);

    // Rata Die day number: rd(1,1,1) = 1. Bijection between valid
    // Gregorian dates and the integers; adding n to a day number moves
    // the date by exactly n days.
    static rational rata_die(rational const& y, rational const& m, rational const& d);

    static void date_of_rata_die(rational const& rd, rational& y, rational& m, rational& d);

    // The three-step date.add algorithm (month normalization, end-of-month
    // clamp, day carry) evaluated on concrete values.
    static void add(rational const& y, rational const& m, rational const& d,
                    rational const& py, rational const& pm, rational const& pd,
                    rational& oy, rational& om, rational& od);
};

class date_util {
    ast_manager&      m;
    family_id         m_fid;
    date_decl_plugin* m_plugin;
    arith_util        m_arith;

public:
    date_util(ast_manager& m):
        m(m),
        m_fid(m.mk_family_id("date")),
        m_plugin(static_cast<date_decl_plugin*>(m.get_plugin(m_fid))),
        m_arith(m) {
    }

    ast_manager& get_manager() const { return m; }
    family_id get_family_id() const { return m_fid; }
    date_decl_plugin& plugin() const { return *m_plugin; }

    sort* mk_date_sort() { return m.mk_sort(m_fid, DATE_SORT); }
    bool is_date(sort* s) const { return is_sort_of(s, m_fid, DATE_SORT); }
    bool is_date(expr* e) const { return is_date(e->get_sort()); }

    app* mk_date(expr* y, expr* mo, expr* d) { expr* args[3] = { y, mo, d }; return m.mk_app(m_fid, OP_DATE_MK, 3, args); }
    app* mk_date(rational const& y, rational const& mo, rational const& d) {
        return mk_date(m_arith.mk_int(y), m_arith.mk_int(mo), m_arith.mk_int(d));
    }
    app* mk_year(expr* d) { return m.mk_app(m_fid, OP_DATE_YEAR, d); }
    app* mk_month(expr* d) { return m.mk_app(m_fid, OP_DATE_MONTH, d); }
    app* mk_day(expr* d) { return m.mk_app(m_fid, OP_DATE_DAY, d); }
    app* mk_add(expr* d, expr* py, expr* pm, expr* pd) { expr* args[4] = { d, py, pm, pd }; return m.mk_app(m_fid, OP_DATE_ADD, 4, args); }
    app* mk_sub(expr* d, expr* py, expr* pm, expr* pd) { expr* args[4] = { d, py, pm, pd }; return m.mk_app(m_fid, OP_DATE_SUB, 4, args); }
    app* mk_lt(expr* d1, expr* d2) { return m.mk_app(m_fid, OP_DATE_LT, d1, d2); }
    app* mk_le(expr* d1, expr* d2) { return m.mk_app(m_fid, OP_DATE_LE, d1, d2); }

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

    // Recognize (date.mk n1 n2 n3) with integer numeral arguments.
    // The triple is not necessarily calendar-valid.
    bool is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d) const {
        return is_mk(e) &&
            m_arith.is_numeral(to_app(e)->get_arg(0), y) &&
            m_arith.is_numeral(to_app(e)->get_arg(1), mo) &&
            m_arith.is_numeral(to_app(e)->get_arg(2), d);
    }

    // Recognize a canonical Date value: a calendar-valid numeral triple.
    bool is_value(expr const* e, rational& y, rational& mo, rational& d) const {
        return is_numeral_mk(e, y, mo, d) && date_decl_plugin::is_valid_date(y, mo, d);
    }
};
