/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declaration plugin for the theory of calendar dates.
    See date_decl_plugin.h for the semantics of the theory.

    The calendar conversions follow Howard Hinnant's days_from_civil /
    civil_from_days algorithms, generalized to unbounded integers.
    All divisions are by positive constants, so SMT-LIB div/mod
    (Euclidean division) coincides with floor division and the same
    formulas can be used both on numerals and on symbolic terms.

Author:

    Angel Cui's date theory task 2026-07-04

--*/
#include "ast/date_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"

date_decl_plugin::~date_decl_plugin() {
    if (m_manager)
        m_manager->dec_ref(m_date);
}

void date_decl_plugin::set_manager(ast_manager* m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_date = m->mk_sort(symbol("Date"), sort_info(m_family_id, DATE_SORT));
    m->inc_ref(m_date);
}

func_decl* date_decl_plugin::mk_decl(decl_kind k, char const* name, unsigned arity, sort* const* domain, sort* range) {
    return m_manager->mk_func_decl(symbol(name), arity, domain, range, func_decl_info(m_family_id, k));
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
    unsigned arity, sort* const* domain, sort* range) {
    ast_manager& m = *m_manager;
    arith_util a(m);
    sort* i = a.mk_int();
    auto check = [&](char const* name, unsigned expected_arity, std::initializer_list<sort*> expected) {
        if (num_parameters != 0)
            m.raise_exception(std::string(name) + ": no parameters expected");
        if (arity != expected_arity)
            m.raise_exception(std::string(name) + ": incorrect number of arguments");
        unsigned j = 0;
        for (sort* s : expected) {
            if (domain[j] != s)
                m.raise_exception(std::string(name) + ": argument " + std::to_string(j + 1) +
                    " has sort " + mk_pp(domain[j], m) + ", expected " + mk_pp(s, m));
            ++j;
        }
    };
    switch (k) {
    case OP_DATE_MK:
        check("date.mk", 3, { i, i, i });
        return mk_decl(k, "date.mk", arity, domain, m_date);
    case OP_DATE_YEAR:
        check("date.year", 1, { m_date });
        return mk_decl(k, "date.year", arity, domain, i);
    case OP_DATE_MONTH:
        check("date.month", 1, { m_date });
        return mk_decl(k, "date.month", arity, domain, i);
    case OP_DATE_DAY:
        check("date.day", 1, { m_date });
        return mk_decl(k, "date.day", arity, domain, i);
    case OP_DATE_ADD:
        check("date.add", 4, { m_date, i, i, i });
        return mk_decl(k, "date.add", arity, domain, m_date);
    case OP_DATE_SUB:
        check("date.sub", 4, { m_date, i, i, i });
        return mk_decl(k, "date.sub", arity, domain, m_date);
    case OP_DATE_LT:
        check("date.lt", 2, { m_date, m_date });
        return mk_decl(k, "date.lt", arity, domain, m.mk_bool_sort());
    case OP_DATE_LE:
        check("date.le", 2, { m_date, m_date });
        return mk_decl(k, "date.le", arity, domain, m.mk_bool_sort());
    case OP_DATE_GT:
        check("date.gt", 2, { m_date, m_date });
        return mk_decl(k, "date.gt", arity, domain, m.mk_bool_sort());
    case OP_DATE_GE:
        check("date.ge", 2, { m_date, m_date });
        return mk_decl(k, "date.ge", arity, domain, m.mk_bool_sort());
    case OP_DATE_EPOCH:
        check("date.epoch", 1, { m_date });
        return mk_decl(k, "date.epoch", arity, domain, i);
    default:
        UNREACHABLE();
        return nullptr;
    }
}

void date_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const& logic) {
    // OP_DATE_EPOCH is deliberately not exposed: it is internal to the theory solvers.
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
    if (!a.is_numeral(e->get_arg(0), y) || !y.is_int() ||
        !a.is_numeral(e->get_arg(1), mo) || !mo.is_int() ||
        !a.is_numeral(e->get_arg(2), d) || !d.is_int())
        return false;
    // values are valid in-range triples
    return is_valid_civil(y, mo, d);
}

bool date_decl_plugin::is_unique_value(app* e) const {
    return is_value(e);
}

bool date_decl_plugin::are_distinct(app* a, app* b) const {
    // valid triples are canonical representations
    return a != b && is_value(a) && is_value(b);
}

expr* date_decl_plugin::get_some_value(sort* s) {
    SASSERT(s == m_date);
    arith_util a(*m_manager);
    expr* args[3] = { a.mk_int(1970), a.mk_int(1), a.mk_int(1) };
    return m_manager->mk_app(m_family_id, OP_DATE_MK, 3, args);
}

// --- concrete calendar arithmetic ------------------------------------

bool date_decl_plugin::is_leap_year(rational const& y) {
    if (!mod(y, rational(4)).is_zero())
        return false;
    if (!mod(y, rational(100)).is_zero())
        return true;
    return mod(y, rational(400)).is_zero();
}

rational date_decl_plugin::days_in_month(rational const& y, rational const& mo) {
    SASSERT(rational::one() <= mo && mo <= rational(12));
    static int const dim[12] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 };
    unsigned m = mo.get_unsigned();
    if (m == 2 && is_leap_year(y))
        return rational(29);
    return rational(dim[m - 1]);
}

bool date_decl_plugin::is_valid_civil(rational const& y, rational const& mo, rational const& d) {
    return
        rational::one() <= y && y <= rational(9999) &&
        rational::one() <= mo && mo <= rational(12) &&
        rational::one() <= d && d <= days_in_month(y, mo);
}

rational date_decl_plugin::min_epoch() {
    return rational(-719162);  // civil_to_days(1, 1, 1)
}

rational date_decl_plugin::max_epoch() {
    return rational(2932896);  // civil_to_days(9999, 12, 31)
}

void date_decl_plugin::normalize_ym(rational& y, rational& mo) {
    rational mm = mo - rational::one();
    rational q = div(mm, rational(12)); // floor division: divisor is positive
    y += q;
    mo = mm - q * rational(12) + rational::one();
    SASSERT(rational::one() <= mo && mo <= rational(12));
}

rational date_decl_plugin::civil_to_days(rational y, rational mo, rational const& d) {
    normalize_ym(y, mo);
    rational yy = (mo <= rational(2)) ? y - rational::one() : y;
    rational era = div(yy, rational(400));
    rational yoe = yy - era * rational(400);                          // [0, 399]
    rational mp = (mo > rational(2)) ? mo - rational(3) : mo + rational(9); // [0, 11], March = 0
    rational doy = div(rational(153) * mp + rational(2), rational(5));
    rational doe = yoe * rational(365) + div(yoe, rational(4)) - div(yoe, rational(100)) + doy;
    return era * rational(146097) + doe - rational(719468) + d - rational::one();
}

void date_decl_plugin::days_to_civil(rational const& n, rational& y, rational& mo, rational& d) {
    rational z = n + rational(719468);
    rational era = div(z, rational(146097));
    rational doe = z - era * rational(146097);                        // [0, 146096]
    rational yoe = div(doe - div(doe, rational(1460)) + div(doe, rational(36524)) - div(doe, rational(146096)),
                       rational(365));                                // [0, 399]
    rational yy = yoe + era * rational(400);
    rational doy = doe - (rational(365) * yoe + div(yoe, rational(4)) - div(yoe, rational(100))); // [0, 365]
    rational mp = div(rational(5) * doy + rational(2), rational(153)); // [0, 11]
    d = doy - div(rational(153) * mp + rational(2), rational(5)) + rational::one(); // [1, 31]
    mo = (mp < rational(10)) ? mp + rational(3) : mp - rational(9);   // [1, 12]
    y = (mo <= rational(2)) ? yy + rational::one() : yy;
}

bool date_decl_plugin::add_to_days_checked(rational const& n, rational const& py, rational const& pm, rational const& pd,
                                           rational& r) {
    rational y, mo, d;
    days_to_civil(n, y, mo, d);
    rational t = y * rational(12) + mo - rational::one() + py * rational(12) + pm;
    rational y2 = div(t, rational(12));
    rational m2 = t - y2 * rational(12) + rational::one();
    if (y2 < rational::one() || y2 > rational(9999))
        return false;
    rational dim = days_in_month(y2, m2);
    if (d > dim)
        d = dim;
    r = civil_to_days(y2, m2, d) + pd;
    return min_epoch() <= r && r <= max_epoch();
}

// --- date_util --------------------------------------------------------

date_util::date_util(ast_manager& m) :
    m(m),
    m_arith(m),
    m_fid(m.mk_family_id("date")) {
    m_plugin = static_cast<date_decl_plugin*>(m.get_plugin(m_fid));
}

bool date_util::is_numeral_mk(expr const* e, rational& y, rational& mo, rational& d) {
    if (!is_mk(e))
        return false;
    app const* a = to_app(e);
    arith_util& au = m_arith;
    return
        au.is_numeral(a->get_arg(0), y) && y.is_int() &&
        au.is_numeral(a->get_arg(1), mo) && mo.is_int() &&
        au.is_numeral(a->get_arg(2), d) && d.is_int();
}

app* date_util::mk_value_from_epoch(rational const& n) {
    rational y, mo, d;
    date_decl_plugin::days_to_civil(n, y, mo, d);
    expr* args[3] = { m_arith.mk_numeral(y, true), m_arith.mk_numeral(mo, true), m_arith.mk_numeral(d, true) };
    return m.mk_app(m_fid, OP_DATE_MK, 3, args);
}

// --- symbolic epoch encodings ------------------------------------------

app* date_util::mk_fresh_int(char const* prefix) {
    return m.mk_fresh_const(prefix, m_arith.mk_int());
}

expr_ref date_util::mk_month_offset(expr* mo, expr* leap01) {
    arith_util& a = m_arith;
    static int const moff[12] = { 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334 };
    expr_ref r(a.mk_int(moff[11]), m);
    for (unsigned i = 11; i-- > 0; )
        r = m.mk_ite(a.mk_le(mo, a.mk_int(i + 1)), a.mk_int(moff[i]), r);
    return expr_ref(a.mk_add(r, m.mk_ite(a.mk_ge(mo, a.mk_int(3)), leap01, a.mk_int(0))), m);
}

expr_ref date_util::mk_days_in_month(expr* mo, expr* leap01) {
    arith_util& a = m_arith;
    expr_ref feb(a.mk_add(a.mk_int(28), leap01), m);
    expr_ref short_month(m.mk_or(m.mk_or(m.mk_eq(mo, a.mk_int(4)), m.mk_eq(mo, a.mk_int(6))),
                                 m.mk_or(m.mk_eq(mo, a.mk_int(9)), m.mk_eq(mo, a.mk_int(11)))), m);
    return expr_ref(m.mk_ite(m.mk_eq(mo, a.mk_int(2)), feb,
                             m.mk_ite(short_month, a.mk_int(30), a.mk_int(31))), m);
}

void date_util::mk_civil_consts(expr_ref& y, expr_ref& mo, expr_ref& d) {
    y = mk_fresh_int("date.y");
    mo = mk_fresh_int("date.m");
    d = mk_fresh_int("date.d");
}

expr_ref date_util::bind_int(char const* prefix, expr* def, int lo, int hi, expr_ref_vector& constraints) {
    expr_ref v(mk_fresh_int(prefix), m);
    constraints.push_back(m.mk_eq(v, def));
    constraints.push_back(m_arith.mk_le(m_arith.mk_int(lo), v));
    constraints.push_back(m_arith.mk_le(v, m_arith.mk_int(hi)));
    return v;
}

expr_ref date_util::mk_year_days(expr* y, expr_ref& leap01, expr_ref_vector& constraints) {
    arith_util& a = m_arith;
    // Euclidean divisions of y - 1 by 4, 100 and 400, in relational form:
    // y - 1 = k*q + s with 0 <= s < k. The remainders determine leap years:
    // y = 0 (mod 4) iff s4 = 3, etc.
    expr_ref y1(a.mk_sub(y, a.mk_int(1)), m);
    expr_ref c4(mk_fresh_int("date.c4"), m), s4(mk_fresh_int("date.s4"), m);
    expr_ref c100(mk_fresh_int("date.c100"), m), s100(mk_fresh_int("date.s100"), m);
    expr_ref c400(mk_fresh_int("date.c400"), m), s400(mk_fresh_int("date.s400"), m);
    constraints.push_back(m.mk_eq(y1, a.mk_add(a.mk_mul(a.mk_int(4), c4), s4)));
    constraints.push_back(a.mk_le(a.mk_int(0), s4));
    constraints.push_back(a.mk_le(s4, a.mk_int(3)));
    constraints.push_back(m.mk_eq(y1, a.mk_add(a.mk_mul(a.mk_int(100), c100), s100)));
    constraints.push_back(a.mk_le(a.mk_int(0), s100));
    constraints.push_back(a.mk_le(s100, a.mk_int(99)));
    constraints.push_back(m.mk_eq(y1, a.mk_add(a.mk_mul(a.mk_int(400), c400), s400)));
    constraints.push_back(a.mk_le(a.mk_int(0), s400));
    constraints.push_back(a.mk_le(s400, a.mk_int(399)));
    expr_ref is_leap(m.mk_or(m.mk_and(m.mk_eq(s4, a.mk_int(3)),
                                      m.mk_not(m.mk_eq(s100, a.mk_int(99)))),
                             m.mk_eq(s400, a.mk_int(399))), m);
    leap01 = bind_int("date.leap", m.mk_ite(is_leap, a.mk_int(1), a.mk_int(0)), 0, 1, constraints);
    // 365*y + (number of leap years in [0, y-1]) + 1
    return expr_ref(a.mk_add(a.mk_mul(a.mk_int(365), y),
                             a.mk_add(c4, a.mk_sub(c400, a.mk_sub(c100, a.mk_int(1))))), m);
}

void date_util::mk_norm_month(expr* months, expr_ref& y2, expr_ref& m2, expr_ref_vector& constraints) {
    arith_util& a = m_arith;
    y2 = mk_fresh_int("date.ny");
    m2 = mk_fresh_int("date.nm");
    constraints.push_back(m.mk_eq(a.mk_add(a.mk_mul(a.mk_int(12), y2), m2),
                                  a.mk_add(months, a.mk_int(1))));
    constraints.push_back(a.mk_le(a.mk_int(1), m2));
    constraints.push_back(a.mk_le(m2, a.mk_int(12)));
}

expr_ref date_util::mk_civil_rep(expr* y, expr* mo, expr* d, expr_ref_vector& constraints) {
    arith_util& a = m_arith;
    expr_ref leap01(m);
    expr_ref yd = mk_year_days(y, leap01, constraints);
    expr_ref mf = bind_int("date.moff", mk_month_offset(mo, leap01), 0, 335, constraints);
    expr_ref dim = bind_int("date.dim", mk_days_in_month(mo, leap01), 28, 31, constraints);
    constraints.push_back(a.mk_le(a.mk_int(1), y));
    constraints.push_back(a.mk_le(y, a.mk_int(9999)));
    constraints.push_back(a.mk_le(a.mk_int(1), mo));
    constraints.push_back(a.mk_le(mo, a.mk_int(12)));
    constraints.push_back(a.mk_le(a.mk_int(1), d));
    constraints.push_back(a.mk_le(d, dim));
    // days-before-year + days-before-month + (d - 1) - epoch offset,
    // where 719528 is the number of days from 0000-01-01 to 1970-01-01
    return expr_ref(a.mk_add(yd, a.mk_add(mf, a.mk_sub(d, a.mk_int(719529)))), m);
}

expr_ref date_util::mk_epoch_add(expr* y0, expr* mo0, expr* d0, expr* py, expr* pm, expr* pd, bool sub,
                                 expr_ref_vector& constraints) {
    arith_util& a = m_arith;
    // shift the zero-based month count, normalize, clamp the day, add pd days
    expr_ref base(a.mk_add(a.mk_mul(a.mk_int(12), y0), a.mk_sub(mo0, a.mk_int(1))), m);
    expr_ref off(a.mk_add(a.mk_mul(a.mk_int(12), py), pm), m);
    expr_ref months(sub ? a.mk_sub(base, off) : a.mk_add(base, off), m);
    expr_ref y2(m), m2(m), leap01(m);
    mk_norm_month(months, y2, m2, constraints);
    // the intermediate date after the month shift must be in range
    constraints.push_back(a.mk_le(a.mk_int(1), y2));
    constraints.push_back(a.mk_le(y2, a.mk_int(9999)));
    expr_ref yd = mk_year_days(y2, leap01, constraints);
    expr_ref mf = bind_int("date.moff", mk_month_offset(m2, leap01), 0, 335, constraints);
    expr_ref dim = bind_int("date.dim", mk_days_in_month(m2, leap01), 28, 31, constraints);
    expr_ref d2 = bind_int("date.cday", m.mk_ite(a.mk_le(d0, dim), d0, dim), 1, 31, constraints);
    constraints.push_back(a.mk_le(d2, dim));   // implied: d2 = min(d0, dim)
    constraints.push_back(a.mk_le(d2, d0));
    expr_ref res(a.mk_add(yd, a.mk_add(mf, a.mk_sub(d2, a.mk_int(719529)))), m);
    return expr_ref(sub ? a.mk_sub(res, pd) : a.mk_add(res, pd), m);
}

// --- explicit side conditions -------------------------------------------
//
// Closed-form (fresh-constant free) formulations of the validity side
// conditions carried by date.mk/date.add/date.sub occurrences. These are
// attached to asserted formulas at the front end, so they survive any
// preprocessing that might drop the occurrences themselves.

expr_ref date_util::mk_leap01_term(expr* y) {
    arith_util& a = m_arith;
    expr_ref div4(m.mk_eq(a.mk_mod(y, a.mk_int(4)), a.mk_int(0)), m);
    expr_ref div100(m.mk_eq(a.mk_mod(y, a.mk_int(100)), a.mk_int(0)), m);
    expr_ref div400(m.mk_eq(a.mk_mod(y, a.mk_int(400)), a.mk_int(0)), m);
    expr_ref is_leap(m.mk_and(div4, m.mk_or(m.mk_not(div100), div400)), m);
    return expr_ref(m.mk_ite(is_leap, a.mk_int(1), a.mk_int(0)), m);
}

expr_ref date_util::mk_ground_epoch(expr* y, expr* mo, expr* d) {
    arith_util& a = m_arith;
    expr_ref y1(a.mk_sub(y, a.mk_int(1)), m);
    expr_ref c4(a.mk_idiv(y1, a.mk_int(4)), m);
    expr_ref c100(a.mk_idiv(y1, a.mk_int(100)), m);
    expr_ref c400(a.mk_idiv(y1, a.mk_int(400)), m);
    // days before year y (counted from 0000-01-01, plus 1) as in mk_year_days
    expr_ref yd(a.mk_add(a.mk_mul(a.mk_int(365), y),
                         a.mk_add(c4, a.mk_sub(c400, a.mk_sub(c100, a.mk_int(1))))), m);
    expr_ref leap01 = mk_leap01_term(y);
    expr_ref mf = mk_month_offset(mo, leap01);
    return expr_ref(a.mk_add(yd, a.mk_add(mf, a.mk_sub(d, a.mk_int(719529)))), m);
}

expr_ref date_util::mk_valid_ymd(expr* y, expr* mo, expr* d) {
    arith_util& a = m_arith;
    expr_ref leap01 = mk_leap01_term(y);
    expr_ref dim = mk_days_in_month(mo, leap01);
    expr_ref_vector cs(m);
    cs.push_back(a.mk_le(a.mk_int(1), y));
    cs.push_back(a.mk_le(y, a.mk_int(9999)));
    cs.push_back(a.mk_le(a.mk_int(1), mo));
    cs.push_back(a.mk_le(mo, a.mk_int(12)));
    cs.push_back(a.mk_le(a.mk_int(1), d));
    cs.push_back(a.mk_le(d, dim));
    return expr_ref(m.mk_and(cs), m);
}

bool date_util::has_guarded_date_term(expr* e) {
    return has_guarded_date_term(m, e);
}

bool date_util::has_guarded_date_term(ast_manager& m, expr* e) {
    family_id fid = m.mk_family_id("date");
    decl_plugin* p = m.get_plugin(fid);
    if (!p)
        return false;
    expr_ref r(e, m);
    for (expr* t : subterms::all(r)) {
        if (!is_app(t) || to_app(t)->get_family_id() != fid)
            continue;
        switch (to_app(t)->get_decl_kind()) {
        case OP_DATE_MK:
        case OP_DATE_ADD:
        case OP_DATE_SUB:
            if (!p->is_value(to_app(t)))
                return true;
            break;
        default:
            break;
        }
    }
    return false;
}

void date_util::mk_occurrence_conditions(expr* f, expr_ref_vector& conds) {
    expr_ref r(f, m);
    for (expr* t : subterms::all(r)) {
        if (!is_ground(t))
            continue;
        app* a2 = to_app(t);
        if (is_mk(t)) {
            rational vy, vm, vd;
            if (is_numeral_mk(t, vy, vm, vd)) {
                if (!date_decl_plugin::is_valid_civil(vy, vm, vd))
                    conds.push_back(m.mk_false());
            }
            else
                conds.push_back(mk_valid_ymd(a2->get_arg(0), a2->get_arg(1), a2->get_arg(2)));
        }
        // date.add/date.sub range conditions are enforced by the theory
        // solvers; preprocessing is kept from dropping such occurrences by
        // the has_guarded_date_term guards in the equation solving passes.
    }
}

expr_ref date_util::attach_side_conditions(expr* f) {
    expr_ref_vector conds(m);
    mk_occurrence_conditions(f, conds);
    if (conds.empty())
        return expr_ref(f, m);
    conds.push_back(f);
    return expr_ref(m.mk_and(conds), m);
}
