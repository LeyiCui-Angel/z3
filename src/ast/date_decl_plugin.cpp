/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declaration plugin for the theory of calendar dates.

Author:

    Date theory extension 2026-07-05

--*/
#include "ast/date_decl_plugin.h"
#include "ast/ast_pp.h"

date_decl_plugin::~date_decl_plugin() {
    if (m_manager) {
        m_manager->dec_ref(m_date);
        m_manager->dec_ref(m_int);
    }
}

void date_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_date = m->mk_sort(symbol("Date"), sort_info(m_family_id, DATE_SORT));
    m->inc_ref(m_date);
    arith_util a(*m);
    m_int = a.mk_int();
    m->inc_ref(m_int);
}

func_decl* date_decl_plugin::mk_decl_checked(decl_kind k, char const* name, unsigned arity, sort* const* domain,
                                             unsigned expected_arity, sort* expected_range) {
    ast_manager& m = *m_manager;
    std::stringstream msg;
    if (arity != expected_arity) {
        msg << "incorrect number of arguments passed to " << name << ". Expected "
            << expected_arity << ", received " << arity;
        m.raise_exception(msg.str());
    }
    for (unsigned i = 0; i < arity; ++i) {
        sort* expected = (k == OP_DATE_MK) ? m_int :
                         (i == 0 || k == OP_DATE_LT || k == OP_DATE_LE || k == OP_DATE_GT || k == OP_DATE_GE) ? m_date :
                         m_int;
        if (domain[i] != expected) {
            msg << "incorrect argument " << (i + 1) << " passed to " << name << ": expected sort "
                << mk_pp(expected, m) << ", received " << mk_pp(domain[i], m);
            m.raise_exception(msg.str());
        }
    }
    return m.mk_func_decl(symbol(name), arity, domain, expected_range, func_decl_info(m_family_id, k));
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                          unsigned arity, sort* const* domain, sort* range) {
    if (num_parameters != 0)
        m_manager->raise_exception("date operators expect no parameters");
    switch (k) {
    case OP_DATE_MK:
        return mk_decl_checked(k, "date.mk", arity, domain, 3, m_date);
    case OP_DATE_YEAR:
        return mk_decl_checked(k, "date.year", arity, domain, 1, m_int);
    case OP_DATE_MONTH:
        return mk_decl_checked(k, "date.month", arity, domain, 1, m_int);
    case OP_DATE_DAY:
        return mk_decl_checked(k, "date.day", arity, domain, 1, m_int);
    case OP_DATE_ADD:
        return mk_decl_checked(k, "date.add", arity, domain, 4, m_date);
    case OP_DATE_SUB:
        return mk_decl_checked(k, "date.sub", arity, domain, 4, m_date);
    case OP_DATE_LT:
        return mk_decl_checked(k, "date.lt", arity, domain, 2, m_manager->mk_bool_sort());
    case OP_DATE_LE:
        return mk_decl_checked(k, "date.le", arity, domain, 2, m_manager->mk_bool_sort());
    case OP_DATE_GT:
        return mk_decl_checked(k, "date.gt", arity, domain, 2, m_manager->mk_bool_sort());
    case OP_DATE_GE:
        return mk_decl_checked(k, "date.ge", arity, domain, 2, m_manager->mk_bool_sort());
    default:
        UNREACHABLE();
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

bool date_decl_plugin::is_value(app* e) const {
    if (!is_app_of(e, m_family_id, OP_DATE_MK))
        return false;
    arith_util a(*m_manager);
    rational y, mo, d;
    if (!a.is_numeral(e->get_arg(0), y) || !a.is_numeral(e->get_arg(1), mo) || !a.is_numeral(e->get_arg(2), d))
        return false;
    return date_util::is_valid_date(y, mo, d);
}

bool date_decl_plugin::is_unique_value(app* e) const {
    return is_value(e);
}

bool date_decl_plugin::are_equal(app* a, app* b) const {
    return a == b;
}

bool date_decl_plugin::are_distinct(app* a, app* b) const {
    return a != b && is_value(a) && is_value(b);
}

expr* date_decl_plugin::get_some_value(sort* s) {
    arith_util a(*m_manager);
    expr* args[3] = { a.mk_int(1), a.mk_int(1), a.mk_int(1) };
    return m_manager->mk_app(m_family_id, OP_DATE_MK, 3, args);
}

// -----------------------------------
// date_util
// -----------------------------------

date_util::date_util(ast_manager& m):
    m_manager(m),
    m_arith(m),
    m_fid(m.mk_family_id("date")),
    m_plugin(static_cast<date_decl_plugin*>(m.get_plugin(m_fid))) {
}

app* date_util::mk_date(rational const& y, rational const& mo, rational const& d) {
    return mk_date(m_arith.mk_int(y), m_arith.mk_int(mo), m_arith.mk_int(d));
}

bool date_util::is_concrete_date(expr const* e, rational& y, rational& mo, rational& d) const {
    if (!is_mk(e))
        return false;
    app const* t = to_app(e);
    return m_arith.is_numeral(t->get_arg(0), y) && y.is_int() &&
           m_arith.is_numeral(t->get_arg(1), mo) && mo.is_int() &&
           m_arith.is_numeral(t->get_arg(2), d) && d.is_int();
}

// -----------------------------------
// concrete calendar arithmetic
// -----------------------------------

bool date_util::is_leap_year(rational const& y) {
    return (mod(y, rational(4)).is_zero() && !mod(y, rational(100)).is_zero()) ||
           mod(y, rational(400)).is_zero();
}

rational date_util::days_in_month(rational const& y, rational const& mo) {
    SASSERT(rational(1) <= mo && mo <= rational(12));
    if (mo == rational(2))
        return rational(is_leap_year(y) ? 29 : 28);
    if (mo == rational(4) || mo == rational(6) || mo == rational(9) || mo == rational(11))
        return rational(30);
    return rational(31);
}

bool date_util::is_valid_date(rational const& y, rational const& mo, rational const& d) {
    if (!y.is_int() || !mo.is_int() || !d.is_int())
        return false;
    if (mo < rational(1) || mo > rational(12))
        return false;
    return rational(1) <= d && d <= days_in_month(y, mo);
}

rational date_util::epoch_of_civil(rational const& y, rational const& mo, rational const& d) {
    // Hinnant's days_from_civil, exact over all integer years
    rational yp  = mo <= rational(2) ? y - rational(1) : y;
    rational era = div(yp, rational(400));
    rational yoe = yp - era * rational(400);
    rational mp  = mod(mo + rational(9), rational(12));
    rational doy = div(rational(153) * mp + rational(2), rational(5)) + d - rational(1);
    rational doe = yoe * rational(365) + div(yoe, rational(4)) - div(yoe, rational(100)) + doy;
    return era * rational(146097) + doe - rational(719468);
}

void date_util::civil_of_epoch(rational const& z, rational& y, rational& mo, rational& d) {
    // Hinnant's civil_from_days, exact over all integers
    rational z2  = z + rational(719468);
    rational era = div(z2, rational(146097));
    rational doe = z2 - era * rational(146097);
    rational yoe = div(doe - div(doe, rational(1460)) + div(doe, rational(36524)) - div(doe, rational(146096)),
                       rational(365));
    rational yy  = yoe + era * rational(400);
    rational doy = doe - (rational(365) * yoe + div(yoe, rational(4)) - div(yoe, rational(100)));
    rational mp  = div(rational(5) * doy + rational(2), rational(153));
    d  = doy - div(rational(153) * mp + rational(2), rational(5)) + rational(1);
    mo = mp < rational(10) ? mp + rational(3) : mp - rational(9);
    y  = mo <= rational(2) ? yy + rational(1) : yy;
}

void date_util::add_period(rational const& y, rational const& mo, rational const& d,
                           rational const& py, rational const& pm, rational const& pd,
                           rational& oy, rational& om, rational& od) {
    SASSERT(is_valid_date(y, mo, d));
    // step 1 -- month normalization
    rational t = mo + rational(12) * py + pm - rational(1);
    oy = y + div(t, rational(12));
    om = mod(t, rational(12)) + rational(1);
    // step 2 -- end-of-month clamp
    rational dim = days_in_month(oy, om);
    rational clamp = d <= dim ? d : dim;
    // step 3 -- day carry, computed via the epoch-day bijection
    civil_of_epoch(epoch_of_civil(oy, om, clamp) + pd, oy, om, od);
}

// -----------------------------------
// integer arithmetic encoding
// -----------------------------------

expr_ref date_util::mk_min(expr* a, expr* b) {
    return expr_ref(m_manager.mk_ite(m_arith.mk_le(a, b), a, b), m_manager);
}

expr_ref date_util::mk_is_leap_expr(expr* y) {
    expr_ref zero(m_arith.mk_int(0), m_manager);
    expr* div4   = m_manager.mk_eq(m_arith.mk_mod(y, m_arith.mk_int(4)), zero);
    expr* div100 = m_manager.mk_eq(m_arith.mk_mod(y, m_arith.mk_int(100)), zero);
    expr* div400 = m_manager.mk_eq(m_arith.mk_mod(y, m_arith.mk_int(400)), zero);
    return expr_ref(m_manager.mk_or(m_manager.mk_and(div4, m_manager.mk_not(div100)), div400), m_manager);
}

expr_ref date_util::mk_days_in_month_expr(expr* y, expr* mo) {
    expr_ref is_feb(m_manager.mk_eq(mo, m_arith.mk_int(2)), m_manager);
    expr_ref feb_days(m_manager.mk_ite(mk_is_leap_expr(y), m_arith.mk_int(29), m_arith.mk_int(28)), m_manager);
    expr_ref is_short(m_manager.mk_or(m_manager.mk_eq(mo, m_arith.mk_int(4)),
                                      m_manager.mk_eq(mo, m_arith.mk_int(6)),
                                      m_manager.mk_eq(mo, m_arith.mk_int(9)),
                                      m_manager.mk_eq(mo, m_arith.mk_int(11))), m_manager);
    expr_ref other_days(m_manager.mk_ite(is_short, m_arith.mk_int(30), m_arith.mk_int(31)), m_manager);
    return expr_ref(m_manager.mk_ite(is_feb, feb_days, other_days), m_manager);
}

expr_ref date_util::mk_valid_expr(expr* y, expr* mo, expr* d) {
    expr_ref one(m_arith.mk_int(1), m_manager);
    expr_ref month_range(m_manager.mk_and(m_arith.mk_le(one, mo), m_arith.mk_le(mo, m_arith.mk_int(12))), m_manager);
    expr_ref day_range(m_manager.mk_and(m_arith.mk_le(one, d), m_arith.mk_le(d, mk_days_in_month_expr(y, mo))), m_manager);
    return expr_ref(m_manager.mk_and(month_range, day_range), m_manager);
}

expr_ref date_util::mk_epoch_expr(expr* y, expr* mo, expr* d) {
    ast_manager& m = m_manager;
    arith_util& a = m_arith;
    // yp = y - (mo <= 2 ? 1 : 0)
    expr_ref yp(a.mk_sub(y, m.mk_ite(a.mk_le(mo, a.mk_int(2)), a.mk_int(1), a.mk_int(0))), m);
    expr_ref era(a.mk_idiv(yp, a.mk_int(400)), m);
    expr_ref yoe(a.mk_sub(yp, a.mk_mul(a.mk_int(400), era)), m);
    expr_ref mp(a.mk_mod(a.mk_add(mo, a.mk_int(9)), a.mk_int(12)), m);
    // doy = (153*mp + 2) div 5 + d - 1
    expr_ref doy(a.mk_add(a.mk_idiv(a.mk_add(a.mk_mul(a.mk_int(153), mp), a.mk_int(2)), a.mk_int(5)),
                          a.mk_sub(d, a.mk_int(1))), m);
    // doe = 365*yoe + yoe div 4 - yoe div 100 + doy
    expr_ref doe(a.mk_add(a.mk_mul(a.mk_int(365), yoe),
                          a.mk_sub(a.mk_idiv(yoe, a.mk_int(4)), a.mk_idiv(yoe, a.mk_int(100))),
                          doy), m);
    return expr_ref(a.mk_add(a.mk_mul(a.mk_int(146097), era), a.mk_sub(doe, a.mk_int(719468))), m);
}

void date_util::mk_civil_expr(expr* z, expr_ref& y, expr_ref& mo, expr_ref& d) {
    ast_manager& m = m_manager;
    arith_util& a = m_arith;
    expr_ref z2(a.mk_add(z, a.mk_int(719468)), m);
    expr_ref era(a.mk_idiv(z2, a.mk_int(146097)), m);
    expr_ref doe(a.mk_sub(z2, a.mk_mul(a.mk_int(146097), era)), m);
    // yoe = (doe - doe div 1460 + doe div 36524 - doe div 146096) div 365
    expr_ref yoe(a.mk_idiv(a.mk_add(a.mk_sub(doe, a.mk_idiv(doe, a.mk_int(1460))),
                                    a.mk_sub(a.mk_idiv(doe, a.mk_int(36524)), a.mk_idiv(doe, a.mk_int(146096)))),
                           a.mk_int(365)), m);
    expr_ref yy(a.mk_add(yoe, a.mk_mul(a.mk_int(400), era)), m);
    // doy = doe - (365*yoe + yoe div 4 - yoe div 100)
    expr_ref doy(a.mk_sub(doe, a.mk_add(a.mk_mul(a.mk_int(365), yoe),
                                        a.mk_sub(a.mk_idiv(yoe, a.mk_int(4)), a.mk_idiv(yoe, a.mk_int(100))))), m);
    expr_ref mp(a.mk_idiv(a.mk_add(a.mk_mul(a.mk_int(5), doy), a.mk_int(2)), a.mk_int(153)), m);
    d = a.mk_add(a.mk_sub(doy, a.mk_idiv(a.mk_add(a.mk_mul(a.mk_int(153), mp), a.mk_int(2)), a.mk_int(5))),
                 a.mk_int(1));
    mo = a.mk_add(mp, m.mk_ite(a.mk_lt(mp, a.mk_int(10)), a.mk_int(3), a.mk_int(-9)));
    y = a.mk_add(yy, m.mk_ite(a.mk_le(mo, a.mk_int(2)), a.mk_int(1), a.mk_int(0)));
}

expr_ref date_util::mk_epoch_of_date(expr* x) {
    return mk_epoch_expr(mk_year(x), mk_month(x), mk_day(x));
}

void date_util::mk_date_term_axioms(expr* x, expr_ref_vector& axioms, expr_ref& recon) {
    ast_manager& m = m_manager;
    expr_ref y(mk_year(x), m), mo(mk_month(x), m), d(mk_day(x), m);
    // every Date value is a calendar-valid Gregorian date
    axioms.push_back(mk_valid_expr(y, mo, d));
    // redundant absolute day bound; cheaper to propagate than the
    // ite-term bound inside the validity constraint
    axioms.push_back(m_arith.mk_le(d, m_arith.mk_int(31)));
    // reconstruction identity
    recon = mk_date(y, mo, d);
    axioms.push_back(m.mk_eq(x, recon));
}

bool date_util::mk_constructor_axioms(app* t, expr_ref_vector& axioms) {
    SASSERT(is_mk(t));
    ast_manager& m = m_manager;
    expr* y = t->get_arg(0);
    expr* mo = t->get_arg(1);
    expr* d = t->get_arg(2);
    rational ny, nm, nd;
    if (is_concrete_date(t, ny, nm, nd)) {
        // fast path: the guard is decided by evaluation
        if (is_valid_date(ny, nm, nd)) {
            axioms.push_back(m.mk_eq(mk_year(t), y));
            axioms.push_back(m.mk_eq(mk_month(t), mo));
            axioms.push_back(m.mk_eq(mk_day(t), d));
        }
        // invalid concrete triple: the constructor value is unspecified
        return true;
    }
    expr_ref valid = mk_valid_expr(y, mo, d);
    axioms.push_back(m.mk_implies(valid, m.mk_eq(mk_year(t), y)));
    axioms.push_back(m.mk_implies(valid, m.mk_eq(mk_month(t), mo)));
    axioms.push_back(m.mk_implies(valid, m.mk_eq(mk_day(t), d)));
    return false;
}

expr_ref date_util::mk_add_axiom(app* t, bool& concrete) {
    SASSERT(is_add(t) || is_sub(t));
    concrete = false;
    ast_manager& m = m_manager;
    arith_util& a = m_arith;
    expr* d = t->get_arg(0);
    expr_ref py(t->get_arg(1), m), pm(t->get_arg(2), m), pd(t->get_arg(3), m);
    if (is_sub(t)) {
        rational v;
        py = a.is_numeral(py, v) ? a.mk_int(-v) : a.mk_uminus(py);
        pm = a.is_numeral(pm, v) ? a.mk_int(-v) : a.mk_uminus(pm);
        pd = a.is_numeral(pd, v) ? a.mk_int(-v) : a.mk_uminus(pd);
    }
    rational ny, nm, nd, vy, vm, vd;
    if (is_concrete_date(d, ny, nm, nd) && is_valid_date(ny, nm, nd) &&
        a.is_numeral(py, vy) && vy.is_int() &&
        a.is_numeral(pm, vm) && vm.is_int() &&
        a.is_numeral(pd, vd) && vd.is_int()) {
        // fast path: evaluate the algorithm on the concrete inputs
        concrete = true;
        rational oy, om, od;
        add_period(ny, nm, nd, vy, vm, vd, oy, om, od);
        return expr_ref(m.mk_and(m.mk_eq(mk_year(t), a.mk_int(oy)),
                                 m.mk_eq(mk_month(t), a.mk_int(om)),
                                 m.mk_eq(mk_day(t), a.mk_int(od))), m);
    }
    if (a.is_numeral(py, vy) && vy.is_zero() && a.is_numeral(pm, vm) && vm.is_zero()) {
        // pure day offset: month normalization is the identity and the
        // end-of-month clamp is absorbed by validity of d, so the result
        // is a plain shift of d's epoch day. Reusing the shared epoch term
        // keeps the reasoning linear.
        return expr_ref(m.mk_eq(mk_epoch_of_date(t), a.mk_add(mk_epoch_of_date(d), pd)), m);
    }
    expr_ref yd(mk_year(d), m), md(mk_month(d), m), dd(mk_day(d), m);
    // step 1 -- month normalization
    expr_ref t0(a.mk_sub(a.mk_add(md, a.mk_mul(a.mk_int(12), py), pm), a.mk_int(1)), m);
    expr_ref oy(a.mk_add(yd, a.mk_idiv(t0, a.mk_int(12))), m);
    expr_ref om(a.mk_add(a.mk_mod(t0, a.mk_int(12)), a.mk_int(1)), m);
    // step 2 -- end-of-month clamp
    expr_ref clamp = mk_min(dd, mk_days_in_month_expr(oy, om));
    // step 3 -- day carry, expressed via the epoch-day bijection
    expr_ref epoch(a.mk_add(mk_epoch_expr(oy, om, clamp), pd), m);
    return expr_ref(m.mk_eq(mk_epoch_of_date(t), epoch), m);
}

expr_ref date_util::mk_compare_rhs(app* p) {
    ast_manager& m = m_manager;
    arith_util& a = m_arith;
    expr* x = p->get_arg(0);
    expr* y = p->get_arg(1);
    expr_ref ex = mk_epoch_of_date(x);
    expr_ref ey = mk_epoch_of_date(y);
    expr_ref cmp(m);
    switch (p->get_decl_kind()) {
    case OP_DATE_LT: cmp = a.mk_lt(ex, ey); break;
    case OP_DATE_LE: cmp = a.mk_le(ex, ey); break;
    case OP_DATE_GT: cmp = a.mk_lt(ey, ex); break;
    case OP_DATE_GE: cmp = a.mk_le(ey, ex); break;
    default: UNREACHABLE();
    }
    return cmp;
}

expr_ref date_util::mk_diseq_axiom(expr* x, expr* y) {
    ast_manager& m = m_manager;
    // distinct valid dates have distinct epoch days
    return expr_ref(m.mk_or(m.mk_eq(x, y),
                            m.mk_not(m.mk_eq(mk_epoch_of_date(x), mk_epoch_of_date(y)))), m);
}
