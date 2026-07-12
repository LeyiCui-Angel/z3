/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.h

Abstract:

    Declaration plugin for the theory of calendar dates.

    The theory introduces the sort Date together with a constructor
    date.mk : Int Int Int -> Date, selectors date.year, date.month,
    date.day, period arithmetic date.add / date.sub, and the
    lexicographic comparisons date.lt / date.le / date.gt / date.ge.

    Date values denote calendar-valid proleptic Gregorian dates with
    unbounded integer years. date.mk is total at the SMT-LIB level;
    its behavior on calendar-invalid triples is unspecified.

Author:

    Date theory extension 2026-07-05

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"

enum date_sort_kind {
    DATE_SORT
};

enum date_op_kind {
    OP_DATE_MK,
    // internal fallback constructor for calendar-invalid concrete triples.
    // The theory leaves such applications unspecified; date.mk0 is treated
    // as an uninterpreted function into Date so that each invalid triple
    // denotes an arbitrary but calendar-valid date, recorded in models.
    OP_DATE_MK0,
    OP_DATE_YEAR,
    OP_DATE_MONTH,
    OP_DATE_DAY,
    OP_DATE_ADD,
    OP_DATE_SUB,
    OP_DATE_LT,
    OP_DATE_LE,
    OP_DATE_GT,
    OP_DATE_GE,
    // internal indicator predicate date.year_pref : Date -> Bool, defined by
    // the theory solvers as year_pref(x) <=> 1 <= date.year(x) <= 9999. Not
    // exposed to users. Its decision phase is forced to true-first so model
    // search prefers human-scale years; the false branch keeps the rest of
    // the unbounded domain reachable, so no model is excluded.
    OP_DATE_YEAR_PREF,
    // fallback tier: year_pref_wide(x) <=> |date.year(x)| <= 999999999,
    // biasing forced-out-of-band years to stay inside the 32-bit range
    OP_DATE_YEAR_PREF_WIDE
};

class date_decl_plugin : public decl_plugin {
    sort* m_date { nullptr };
    sort* m_int { nullptr };

    void set_manager(ast_manager * m, family_id id) override;

    func_decl* mk_decl_checked(decl_kind k, char const* name, unsigned arity, sort* const* domain,
                               unsigned expected_arity, sort* expected_range);

public:
    date_decl_plugin() = default;

    ~date_decl_plugin() override;

    void finalize() override {}

    decl_plugin* mk_fresh() override { return alloc(date_decl_plugin); }

    sort* mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override { return m_date; }

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
        unsigned arity, sort* const* domain, sort* range) override;

    void get_op_names(svector<builtin_name>& op_names, symbol const& logic) override;

    void get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) override;

    bool is_value(app* e) const override;

    bool is_unique_value(app* e) const override;

    // date.mk0 applications denote unspecified (but calendar-valid) dates;
    // models carry an explicit interpretation for them
    bool is_considered_uninterpreted(func_decl* f) override {
        return f->get_family_id() == m_family_id && f->get_decl_kind() == OP_DATE_MK0;
    }

    bool are_equal(app* a, app* b) const override;

    bool are_distinct(app* a, app* b) const override;

    expr* get_some_value(sort* s) override;

    sort* date_sort() const { return m_date; }
};

/**
   \brief Utility for constructing and recognizing date terms, for
   concrete (rational-based) calendar arithmetic, and for building the
   integer-arithmetic encoding of the date axioms used by the theory
   solvers.
*/
class date_util {
    ast_manager&       m_manager;
    arith_util         m_arith;
    family_id          m_fid;
    date_decl_plugin*  m_plugin;

    expr_ref mk_min(expr* a, expr* b);

public:
    date_util(ast_manager& m);

    ast_manager& get_manager() const { return m_manager; }
    family_id get_family_id() const { return m_fid; }
    arith_util& arith() { return m_arith; }
    date_decl_plugin& plugin() const { return *m_plugin; }

    sort* mk_date_sort() { return m_plugin->date_sort(); }
    bool is_date(sort* s) const { return is_sort_of(s, m_fid, DATE_SORT); }
    bool is_date(expr* e) const { return is_date(e->get_sort()); }

    app* mk_date(expr* y, expr* mo, expr* d) { expr* args[3] = { y, mo, d }; return m_manager.mk_app(m_fid, OP_DATE_MK, 3, args); }
    app* mk_date(rational const& y, rational const& mo, rational const& d);
    app* mk_date0(expr* y, expr* mo, expr* d) { expr* args[3] = { y, mo, d }; return m_manager.mk_app(m_fid, OP_DATE_MK0, 3, args); }
    app* mk_year(expr* d)  { return m_manager.mk_app(m_fid, OP_DATE_YEAR, d); }
    app* mk_month(expr* d) { return m_manager.mk_app(m_fid, OP_DATE_MONTH, d); }
    app* mk_day(expr* d)   { return m_manager.mk_app(m_fid, OP_DATE_DAY, d); }
    app* mk_lt(expr* a, expr* b) { return m_manager.mk_app(m_fid, OP_DATE_LT, a, b); }
    app* mk_le(expr* a, expr* b) { return m_manager.mk_app(m_fid, OP_DATE_LE, a, b); }
    app* mk_year_pref(expr* d) { return m_manager.mk_app(m_fid, OP_DATE_YEAR_PREF, d); }
    app* mk_year_pref_wide(expr* d) { return m_manager.mk_app(m_fid, OP_DATE_YEAR_PREF_WIDE, d); }
    app* mk_add(expr* d, expr* py, expr* pm, expr* pd) { expr* args[4] = { d, py, pm, pd }; return m_manager.mk_app(m_fid, OP_DATE_ADD, 4, args); }

    bool is_mk(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_MK); }
    bool is_mk0(expr const* e)   const { return is_app_of(e, m_fid, OP_DATE_MK0); }
    bool is_year(expr const* e)  const { return is_app_of(e, m_fid, OP_DATE_YEAR); }
    bool is_month(expr const* e) const { return is_app_of(e, m_fid, OP_DATE_MONTH); }
    bool is_day(expr const* e)   const { return is_app_of(e, m_fid, OP_DATE_DAY); }
    bool is_add(expr const* e)   const { return is_app_of(e, m_fid, OP_DATE_ADD); }
    bool is_sub(expr const* e)   const { return is_app_of(e, m_fid, OP_DATE_SUB); }
    bool is_lt(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_LT); }
    bool is_le(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_LE); }
    bool is_gt(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_GT); }
    bool is_ge(expr const* e)    const { return is_app_of(e, m_fid, OP_DATE_GE); }
    bool is_year_pref(expr const* e) const {
        return is_app_of(e, m_fid, OP_DATE_YEAR_PREF) || is_app_of(e, m_fid, OP_DATE_YEAR_PREF_WIDE);
    }

    // e is (date.mk n1 n2 n3) for integer numerals n1, n2, n3 (not necessarily calendar-valid)
    bool is_concrete_date(expr const* e, rational& y, rational& mo, rational& d) const;

    // -- concrete calendar arithmetic (proleptic Gregorian, unbounded years) --

    static bool is_leap_year(rational const& y);
    static rational days_in_month(rational const& y, rational const& mo);
    static bool is_valid_date(rational const& y, rational const& mo, rational const& d);
    // days since 1970-01-01 (Hinnant's days_from_civil)
    static rational epoch_of_civil(rational const& y, rational const& mo, rational const& d);
    // inverse of epoch_of_civil (Hinnant's civil_from_days)
    static void civil_of_epoch(rational const& z, rational& y, rational& mo, rational& d);
    // the date.add algorithm: month normalization, end-of-month clamp, day carry
    static void add_period(rational const& y, rational const& mo, rational const& d,
                           rational const& py, rational const& pm, rational const& pd,
                           rational& oy, rational& om, rational& od);

    // -- integer arithmetic encoding of the date semantics --

    // Gregorian leap year condition on integer term y
    expr_ref mk_is_leap_expr(expr* y);
    // number of days of month mo in year y, as an ite-term
    expr_ref mk_days_in_month_expr(expr* y, expr* mo);
    // calendar-validity of the triple (y, mo, d)
    expr_ref mk_valid_expr(expr* y, expr* mo, expr* d);
    // decision-phase preference atoms 1 <= (date.year x) <= 9999. These are
    // never asserted: the theory solvers internalize them and set their
    // decision phase to true-first, so model search tries human-scale years
    // before the unbounded remainder of the integer domain. Semantics are
    // unchanged; only which model of a satisfiable instance is produced.
    void mk_year_prefs(expr* x, expr_ref& lo, expr_ref& hi);
    // fallback preference tier |year| <= 999999999 (inside 32-bit range)
    void mk_year_prefs_wide(expr* x, expr_ref& lo, expr_ref& hi);
    // days since 1970-01-01 of the (assumed valid) triple (y, mo, d)
    expr_ref mk_epoch_expr(expr* y, expr* mo, expr* d);
    // inverse conversion: the civil triple of epoch day z
    void mk_civil_expr(expr* z, expr_ref& y, expr_ref& mo, expr_ref& d);
    // epoch term for the selector triple of date term x
    expr_ref mk_epoch_of_date(expr* x);
    // exact linear envelope linking mk_epoch_of_date(x) to date.year(x);
    // redundant fact instantiated wherever an epoch tower is materialized
    expr_ref mk_epoch_envelope(expr* x);

    /**
       Axioms asserted for every term x of sort Date:
       - calendar validity of (date.year x, date.month x, date.day x),
       - the reconstruction identity x = (date.mk (date.year x) ...),
       - the round-trip identity of the selector triple with its epoch day.
       The generated date.mk term is returned in recon so that callers can
       exempt it from further axiom instantiation.
    */
    void mk_date_term_axioms(expr* x, expr_ref_vector& axioms, expr_ref& recon);

    // for t = (date.mk y mo d): validity of (y, mo, d) implies the selector
    // equations. Returns true when the triple is concrete and the axioms were
    // evaluated; such axioms are in final form and must not be simplified
    // (the date rewriter would fold them to true).
    bool mk_constructor_axioms(app* t, expr_ref_vector& axioms);

    // redundant linear bracket between the year selectors of a pure
    // day-offset result t and its base d; true when pd is not a numeral
    expr_ref mk_year_bracket(expr* t, expr* d, expr* pd);

    // bounded unrolling of the day-carry loop for a numeral day offset vd;
    // pure ite/linear encoding of date.add(d, 0, 0, vd) with no epoch towers
    expr_ref mk_day_carry_unrolled(app* t, expr* d, rational const& vd);

    // for a = (date.add d py pm pd) or (date.sub d py pm pd): the defining
    // axiom for the result. Sets concrete (with the same meaning as for
    // mk_constructor_axioms) when all inputs were evaluated; sets uses_epoch
    // when the returned encoding materializes epoch-day towers (callers then
    // instantiate the epoch envelope for the result and base terms).
    expr_ref mk_add_axiom(app* a, bool& concrete, bool& uses_epoch);

    // for an atom p in {date.lt, date.le, date.gt, date.ge}: the epoch
    // comparison that p is equivalent to; on valid dates the epoch order
    // coincides with the lexicographic order on (year, month, day)
    expr_ref mk_compare_rhs(app* p);

    // for dates asserted distinct: x = y or epoch(x) != epoch(y)
    expr_ref mk_diseq_axiom(expr* x, expr* y);
};
