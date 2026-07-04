/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_decl_plugin.cpp

Abstract:

    Declarations for the theory of calendar dates.

Author:

    Claude (Anthropic) 2026-07-04

--*/
#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"

date_decl_plugin::~date_decl_plugin() {
    if (m_manager)
        m_manager->dec_ref(m_date);
}

void date_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_date = m->mk_sort(symbol("Date"), sort_info(m_family_id, DATE_SORT));
    m->inc_ref(m_date);
}

sort* date_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) {
    if (k != DATE_SORT || num_parameters != 0) {
        m_manager->raise_exception("unsupported date sort");
        return nullptr;
    }
    return m_date;
}

func_decl* date_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                          unsigned arity, sort* const* domain, sort* range) {
    ast_manager& m = *m_manager;
    arith_util a(m);
    sort* i = a.mk_int();
    std::stringstream msg;

    auto check = [&](char const* name, std::initializer_list<sort*> expected) -> bool {
        if (num_parameters != 0) {
            msg << name << ": no parameters expected";
            return false;
        }
        if (arity != expected.size()) {
            msg << name << ": incorrect number of arguments. Expected " << expected.size() << ", received " << arity;
            return false;
        }
        unsigned idx = 0;
        for (sort* s : expected) {
            if (domain[idx] != s) {
                msg << name << ": argument " << (idx + 1) << " has sort " << mk_pp(domain[idx], m)
                    << ", expected " << mk_pp(s, m);
                return false;
            }
            ++idx;
        }
        return true;
    };

    switch (k) {
    case OP_DATE_MK:
        if (check("date.mk", { i, i, i }))
            return m.mk_func_decl(symbol("date.mk"), arity, domain, m_date, func_decl_info(m_family_id, k));
        break;
    case OP_DATE_YEAR:
        if (check("date.year", { m_date }))
            return m.mk_func_decl(symbol("date.year"), arity, domain, i, func_decl_info(m_family_id, k));
        break;
    case OP_DATE_MONTH:
        if (check("date.month", { m_date }))
            return m.mk_func_decl(symbol("date.month"), arity, domain, i, func_decl_info(m_family_id, k));
        break;
    case OP_DATE_DAY:
        if (check("date.day", { m_date }))
            return m.mk_func_decl(symbol("date.day"), arity, domain, i, func_decl_info(m_family_id, k));
        break;
    case OP_DATE_ADD:
        if (check("date.add", { m_date, i, i, i }))
            return m.mk_func_decl(symbol("date.add"), arity, domain, m_date, func_decl_info(m_family_id, k));
        break;
    case OP_DATE_SUB:
        if (check("date.sub", { m_date, i, i, i }))
            return m.mk_func_decl(symbol("date.sub"), arity, domain, m_date, func_decl_info(m_family_id, k));
        break;
    case OP_DATE_LT:
        if (check("date.lt", { m_date, m_date }))
            return m.mk_func_decl(symbol("date.lt"), arity, domain, m.mk_bool_sort(), func_decl_info(m_family_id, k));
        break;
    case OP_DATE_LE:
        if (check("date.le", { m_date, m_date }))
            return m.mk_func_decl(symbol("date.le"), arity, domain, m.mk_bool_sort(), func_decl_info(m_family_id, k));
        break;
    case OP_DATE_GT:
        if (check("date.gt", { m_date, m_date }))
            return m.mk_func_decl(symbol("date.gt"), arity, domain, m.mk_bool_sort(), func_decl_info(m_family_id, k));
        break;
    case OP_DATE_GE:
        if (check("date.ge", { m_date, m_date }))
            return m.mk_func_decl(symbol("date.ge"), arity, domain, m.mk_bool_sort(), func_decl_info(m_family_id, k));
        break;
    default:
        msg << "unsupported date operator";
        break;
    }
    m.raise_exception(msg.str());
    return nullptr;
}

void date_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const& logic) {
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
    date_util u(*m_manager);
    return u.is_value(e);
}

bool date_decl_plugin::is_unique_value(app* e) const {
    // valid concrete triples are canonical: two different valid triples
    // denote different dates
    return is_value(e);
}

bool date_decl_plugin::are_distinct(app* a, app* b) const {
    return a != b && is_value(a) && is_value(b);
}

expr* date_decl_plugin::get_some_value(sort* s) {
    SASSERT(s == m_date);
    date_util u(*m_manager);
    return u.mk_date(rational(1970), rational(1), rational(1));
}

// -----------------------------------
// date_util
// -----------------------------------

date_util::date_util(ast_manager& m):
    m(m),
    m_arith(m),
    m_fid(m.mk_family_id("date")) {
    m_plugin = static_cast<date_decl_plugin*>(m.get_plugin(m_fid));
}

app* date_util::mk_date(rational const& y, rational const& mo, rational const& d) {
    return mk_date(m_arith.mk_int(y), m_arith.mk_int(mo), m_arith.mk_int(d));
}

bool date_util::is_concrete_mk(expr const* e, rational& y, rational& mo, rational& d) const {
    return is_mk(e) &&
        m_arith.is_numeral(to_app(e)->get_arg(0), y) &&
        m_arith.is_numeral(to_app(e)->get_arg(1), mo) &&
        m_arith.is_numeral(to_app(e)->get_arg(2), d) &&
        y.is_int() && mo.is_int() && d.is_int();
}

bool date_util::is_value(expr const* e) const {
    rational y, mo, d;
    return is_concrete_mk(e, y, mo, d) && is_valid_date(y, mo, d);
}

// -----------------------------------
// concrete calendar arithmetic
// -----------------------------------

bool date_util::is_leap_year(rational const& y) {
    rational const four(4), hundred(100), fourhundred(400);
    return (mod(y, four).is_zero() && !mod(y, hundred).is_zero()) || mod(y, fourhundred).is_zero();
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
    return rational(1) <= mo && mo <= rational(12) && rational(1) <= d && d <= days_in_month(y, mo);
}

rational date_util::civil_to_days(rational const& y, rational const& mo, rational const& d) {
    // H. Hinnant, days_from_civil; div is floor division (positive divisors)
    rational yy  = (mo <= rational(2)) ? y - rational(1) : y;
    rational era = div(yy, rational(400));
    rational yoe = yy - era * rational(400);
    rational doy = div(rational(153) * (mo + (mo > rational(2) ? rational(-3) : rational(9))) + rational(2), rational(5)) + d - rational(1);
    rational doe = yoe * rational(365) + div(yoe, rational(4)) - div(yoe, rational(100)) + doy;
    return era * rational(146097) + doe - rational(719468);
}

void date_util::days_to_civil(rational const& zin, rational& y, rational& mo, rational& d) {
    // H. Hinnant, civil_from_days
    rational z   = zin + rational(719468);
    rational era = div(z, rational(146097));
    rational doe = z - era * rational(146097);
    rational yoe = div(doe - div(doe, rational(1460)) + div(doe, rational(36524)) - div(doe, rational(146096)), rational(365));
    rational doy = doe - (rational(365) * yoe + div(yoe, rational(4)) - div(yoe, rational(100)));
    rational mp  = div(rational(5) * doy + rational(2), rational(153));
    d  = doy - div(rational(153) * mp + rational(2), rational(5)) + rational(1);
    mo = mp + (mp < rational(10) ? rational(3) : rational(-9));
    y  = yoe + era * rational(400) + (mo <= rational(2) ? rational(1) : rational(0));
}

void date_util::add_period(rational const& y, rational const& mo, rational const& d,
                           rational const& py, rational const& pm, rational const& pd,
                           rational& ry, rational& rm, rational& rd) {
    SASSERT(is_valid_date(y, mo, d));
    // 1. month normalization
    rational t  = mo + rational(12) * py + pm - rational(1);
    rational y1 = y + div(t, rational(12));
    rational m1 = mod(t, rational(12)) + rational(1);
    // 2. end-of-month clamp
    rational d1 = d;
    rational dim = days_in_month(y1, m1);
    if (d1 > dim)
        d1 = dim;
    // 3. day carry
    days_to_civil(civil_to_days(y1, m1, d1) + pd, ry, rm, rd);
}

// -----------------------------------
// folding builders
// -----------------------------------

expr_ref date_util::num(rational const& v) {
    return expr_ref(m_arith.mk_int(v), m);
}

bool date_util::get_num(expr* e, rational& v) const {
    return m_arith.is_numeral(e, v) && v.is_int();
}

expr_ref date_util::fadd(expr* x, expr* y) {
    rational a, b;
    if (get_num(x, a) && get_num(y, b))
        return num(a + b);
    if (get_num(x, a) && a.is_zero())
        return expr_ref(y, m);
    if (get_num(y, b) && b.is_zero())
        return expr_ref(x, m);
    return expr_ref(m_arith.mk_add(x, y), m);
}

expr_ref date_util::fadd(expr* x, rational const& c) {
    return fadd(x, num(c));
}

expr_ref date_util::fmul(rational const& c, expr* x) {
    rational a;
    if (get_num(x, a))
        return num(c * a);
    if (c.is_one())
        return expr_ref(x, m);
    if (c.is_zero())
        return num(rational(0));
    return expr_ref(m_arith.mk_mul(num(c), x), m);
}

expr_ref date_util::fidiv(expr* x, rational const& c) {
    SASSERT(c.is_pos());
    rational a;
    if (get_num(x, a))
        return num(div(a, c));
    return expr_ref(m_arith.mk_idiv(x, num(c)), m);
}

expr_ref date_util::fmod(expr* x, rational const& c) {
    SASSERT(c.is_pos());
    rational a;
    if (get_num(x, a))
        return num(mod(a, c));
    return expr_ref(m_arith.mk_mod(x, num(c)), m);
}

expr_ref date_util::fle(expr* x, expr* y) {
    rational a, b;
    if (get_num(x, a) && get_num(y, b))
        return expr_ref(m.mk_bool_val(a <= b), m);
    return expr_ref(m_arith.mk_le(x, y), m);
}

expr_ref date_util::feq(expr* x, expr* y) {
    rational a, b;
    if (get_num(x, a) && get_num(y, b))
        return expr_ref(m.mk_bool_val(a == b), m);
    if (x == y)
        return expr_ref(m.mk_true(), m);
    return expr_ref(m.mk_eq(x, y), m);
}

expr_ref date_util::fite(expr* c, expr* t, expr* e) {
    if (m.is_true(c) || t == e)
        return expr_ref(t, m);
    if (m.is_false(c))
        return expr_ref(e, m);
    return expr_ref(m.mk_ite(c, t, e), m);
}

// -----------------------------------
// symbolic builders
// -----------------------------------

expr_ref date_util::mk_is_leap(expr* y) {
    rational v;
    if (get_num(y, v))
        return expr_ref(m.mk_bool_val(is_leap_year(v)), m);
    expr_ref m4(feq(fmod(y, rational(4)), num(rational(0))), m);
    expr_ref m100(feq(fmod(y, rational(100)), num(rational(0))), m);
    expr_ref m400(feq(fmod(y, rational(400)), num(rational(0))), m);
    return expr_ref(m.mk_or(m.mk_and(m4, m.mk_not(m100)), m400), m);
}

expr_ref date_util::mk_days_in_month(expr* y, expr* mo) {
    rational vy, vm;
    if (get_num(mo, vm) && rational(1) <= vm && vm <= rational(12)) {
        if (vm == rational(2))
            return fite(mk_is_leap(y), num(rational(29)), num(rational(28)));
        return num(days_in_month(vy /* unused for mo != 2 */, vm));
    }
    expr_ref feb(fite(mk_is_leap(y), num(rational(29)), num(rational(28))), m);
    expr_ref is_feb(feq(mo, num(rational(2))), m);
    expr_ref is_30(m.mk_or(feq(mo, num(rational(4))), feq(mo, num(rational(6))),
                           feq(mo, num(rational(9))), feq(mo, num(rational(11)))), m);
    return fite(is_feb, feb, fite(is_30, num(rational(30)), num(rational(31))));
}

expr_ref date_util::mk_is_valid(expr* y, expr* mo, expr* d) {
    rational vy, vm, vd;
    if (get_num(y, vy) && get_num(mo, vm) && get_num(d, vd))
        return expr_ref(m.mk_bool_val(is_valid_date(vy, vm, vd)), m);
    expr_ref_vector conj(m);
    conj.push_back(fle(num(rational(1)), mo));
    conj.push_back(fle(mo, num(rational(12))));
    conj.push_back(fle(num(rational(1)), d));
    conj.push_back(fle(d, mk_days_in_month(y, mo)));
    return expr_ref(m.mk_and(conj), m);
}

expr_ref date_util::mk_civil_to_days(expr* y, expr* mo, expr* d) {
    rational vy, vm, vd;
    if (get_num(y, vy) && get_num(mo, vm) && get_num(d, vd) && is_valid_date(vy, vm, vd))
        return num(civil_to_days(vy, vm, vd));
    expr_ref yy(m), mdays(m);
    rational vmo;
    if (get_num(mo, vmo)) {
        yy = fadd(y, vmo <= rational(2) ? rational(-1) : rational(0));
        mdays = num(div(rational(153) * (vmo + (vmo > rational(2) ? rational(-3) : rational(9))) + rational(2), rational(5)));
    }
    else {
        yy = fite(fle(mo, num(rational(2))), fadd(y, rational(-1)), y);
        expr_ref mshift(fite(fle(mo, num(rational(2))), fadd(mo, rational(9)), fadd(mo, rational(-3))), m);
        mdays = fidiv(fadd(fmul(rational(153), mshift), rational(2)), rational(5));
    }
    expr_ref era(fidiv(yy, rational(400)), m);
    expr_ref yoe(fadd(yy, fmul(rational(-400), era)), m);
    expr_ref doy(fadd(mdays, fadd(d, rational(-1))), m);
    expr_ref doe(fadd(fmul(rational(365), yoe),
                 fadd(fidiv(yoe, rational(4)),
                 fadd(fmul(rational(-1), fidiv(yoe, rational(100))), doy))), m);
    return fadd(fmul(rational(146097), era), fadd(doe, rational(-719468)));
}

void date_util::mk_days_to_civil(expr* zin, expr_ref& y, expr_ref& mo, expr_ref& d) {
    rational vz;
    if (get_num(zin, vz)) {
        rational ry, rm, rd;
        days_to_civil(vz, ry, rm, rd);
        y = num(ry); mo = num(rm); d = num(rd);
        return;
    }
    expr_ref z(fadd(zin, rational(719468)), m);
    expr_ref era(fidiv(z, rational(146097)), m);
    expr_ref doe(fadd(z, fmul(rational(-146097), era)), m);
    expr_ref yoe(fidiv(fadd(doe,
                       fadd(fmul(rational(-1), fidiv(doe, rational(1460))),
                       fadd(fidiv(doe, rational(36524)),
                            fmul(rational(-1), fidiv(doe, rational(146096)))))),
                       rational(365)), m);
    expr_ref doy(fadd(doe, fmul(rational(-1),
                 fadd(fmul(rational(365), yoe),
                 fadd(fidiv(yoe, rational(4)),
                      fmul(rational(-1), fidiv(yoe, rational(100))))))), m);
    expr_ref mp(fidiv(fadd(fmul(rational(5), doy), rational(2)), rational(153)), m);
    d  = fadd(fadd(doy, fmul(rational(-1), fidiv(fadd(fmul(rational(153), mp), rational(2)), rational(5)))), rational(1));
    mo = fite(fle(mp, num(rational(9))), fadd(mp, rational(3)), fadd(mp, rational(-9)));
    y  = fadd(fadd(yoe, fmul(rational(400), era)), fite(fle(mo, num(rational(2))), num(rational(1)), num(rational(0))));
}

void date_util::components(expr* d, expr_ref& y, expr_ref& mo, expr_ref& dd) {
    rational vy, vm, vd;
    if (is_concrete_mk(d, vy, vm, vd) && is_valid_date(vy, vm, vd)) {
        y = num(vy); mo = num(vm); dd = num(vd);
        return;
    }
    y = mk_year(d); mo = mk_month(d); dd = mk_day(d);
}

expr_ref date_util::mk_epoch(expr* d) {
    expr_ref y(m), mo(m), dd(m);
    components(d, y, mo, dd);
    return mk_civil_to_days(y, mo, dd);
}

// -----------------------------------
// operation specs
// -----------------------------------

void date_util::mk_valid_spec(expr* y, expr* mo, expr* d, expr_ref_vector& fmls) {
    fmls.push_back(fle(num(rational(1)), mo));
    fmls.push_back(fle(mo, num(rational(12))));
    fmls.push_back(fle(num(rational(1)), d));
    fmls.push_back(fle(d, mk_days_in_month(y, mo)));
}

void date_util::mk_mk_spec(expr* y, expr* mo, expr* d, expr* ty, expr* tm, expr* td, expr_ref_vector& fmls) {
    rational vy, vm, vd;
    if (get_num(y, vy) && get_num(mo, vm) && get_num(d, vd)) {
        if (is_valid_date(vy, vm, vd)) {
            fmls.push_back(feq(ty, y));
            fmls.push_back(feq(tm, mo));
            fmls.push_back(feq(td, d));
        }
        // invalid concrete triple: the term is unconstrained (fresh valid date)
        return;
    }
    expr_ref valid(mk_is_valid(y, mo, d), m);
    expr_ref nvalid(m.mk_not(valid), m);
    fmls.push_back(m.mk_or(nvalid, feq(ty, y)));
    fmls.push_back(m.mk_or(nvalid, feq(tm, mo)));
    fmls.push_back(m.mk_or(nvalid, feq(td, d)));
}

void date_util::mk_add_spec(expr* by, expr* bm, expr* bd,
                            expr* py, expr* pm, expr* pd, bool sub,
                            expr* ry, expr* rm, expr* rd,
                            expr_ref_vector& fmls) {
    rational sign(sub ? -1 : 1);
    expr_ref spy(fmul(sign, py), m), spm(fmul(sign, pm), m), spd(fmul(sign, pd), m);

    // 1. month normalization: t = bm + 12*py + pm - 1
    expr_ref moff(fadd(fmul(rational(12), spy), spm), m);
    expr_ref y1(m), m1(m);
    rational vmoff;
    if (get_num(moff, vmoff) && vmoff.is_zero()) {
        // month and year are unchanged
        y1 = by;
        m1 = bm;
    }
    else {
        expr_ref t(fadd(bm, fadd(moff, rational(-1))), m);
        y1 = fadd(by, fidiv(t, rational(12)));
        m1 = fadd(fmod(t, rational(12)), rational(1));
    }

    // 2. end-of-month clamp: d1 = min(bd, days_in_month(y1, m1))
    expr_ref d1(m);
    if (m1 == bm && y1 == by)
        // same month: the clamp is a no-op since bd is calendar-valid
        d1 = bd;
    else {
        expr_ref dim(mk_days_in_month(y1, m1), m);
        d1 = fite(fle(bd, dim), bd, dim);
    }

    // 3. day carry through the epoch bijection
    rational vpd;
    if (get_num(spd, vpd) && vpd.is_zero()) {
        // no day offset: the result is (y1, m1, d1) directly
        fmls.push_back(feq(ry, y1));
        fmls.push_back(feq(rm, m1));
        fmls.push_back(feq(rd, d1));
        return;
    }
    expr_ref epoch(fadd(mk_civil_to_days(y1, m1, d1), spd), m);
    // constructive definition of the result components
    expr_ref cy(m), cm(m), cd(m);
    mk_days_to_civil(epoch, cy, cm, cd);
    fmls.push_back(feq(ry, cy));
    fmls.push_back(feq(rm, cm));
    fmls.push_back(feq(rd, cd));
    // epoch coherence: the epoch of the result equals the computed epoch.
    // This is entailed, but gives the arithmetic solver a direct route for
    // reasoning about compositions of date arithmetic and comparisons.
    fmls.push_back(feq(mk_civil_to_days(ry, rm, rd), epoch));
}

void date_util::mk_term_spec(expr* t, expr_ref_vector& fmls) {
    SASSERT(is_date(t));
    expr_ref ty(mk_year(t), m), tm(mk_month(t), m), td(mk_day(t), m);
    mk_valid_spec(ty, tm, td, fmls);
    if (is_mk(t)) {
        app* a = to_app(t);
        mk_mk_spec(a->get_arg(0), a->get_arg(1), a->get_arg(2), ty, tm, td, fmls);
    }
    else if (is_add(t) || is_sub(t)) {
        app* a = to_app(t);
        expr_ref by(m), bm(m), bd(m);
        components(a->get_arg(0), by, bm, bd);
        mk_add_spec(by, bm, bd, a->get_arg(1), a->get_arg(2), a->get_arg(3), is_sub(t), ty, tm, td, fmls);
    }
}

expr_ref date_util::mk_cmp_spec(decl_kind k, expr* a, expr* b) {
    // chronological order coincides with the order on epoch day numbers
    expr_ref ea(mk_epoch(a), m);
    expr_ref eb(mk_epoch(b), m);
    rational va, vb;
    bool ground = get_num(ea, va) && get_num(eb, vb);
    switch (k) {
    case OP_DATE_LT:
        return ground ? expr_ref(m.mk_bool_val(va < vb), m) : expr_ref(m_arith.mk_lt(ea, eb), m);
    case OP_DATE_LE:
        return ground ? expr_ref(m.mk_bool_val(va <= vb), m) : expr_ref(m_arith.mk_le(ea, eb), m);
    case OP_DATE_GT:
        return ground ? expr_ref(m.mk_bool_val(va > vb), m) : expr_ref(m_arith.mk_gt(ea, eb), m);
    case OP_DATE_GE:
        return ground ? expr_ref(m.mk_bool_val(va >= vb), m) : expr_ref(m_arith.mk_ge(ea, eb), m);
    default:
        UNREACHABLE();
        return expr_ref(m);
    }
}
