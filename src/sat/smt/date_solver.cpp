/*++
Copyright (c) 2026 CMU PASTA Lab

Module Name:

    date_solver.cpp

Abstract:

    Implementation of the Date theory solver for the SAT/EUF core.

Author:

    Angel Cui

--*/

#include "sat/smt/date_solver.h"
#include "sat/smt/euf_solver.h"

namespace date {

// ============================================================
// Construction
// ============================================================

solver::solver(euf::solver& ctx, theory_id id)
    : th_euf_solver(ctx, ctx.get_manager().get_family_name(id), id),
      m_util(m),
      m_autil(m)
{}

euf::th_solver* solver::clone(euf::solver& ctx) {
    return alloc(solver, ctx, get_id());
}

// ============================================================
// Internalization entry points
// ============================================================

sat::literal solver::internalize(expr* e, bool sign, bool root) {
    if (!visit_rec(m, e, sign, root))
        return sat::null_literal;
    auto lit = ctx.expr2literal(e);
    if (sign) lit.neg();
    return lit;
}

void solver::internalize(expr* e) {
    visit_rec(m, e, false, false);
}

bool solver::visit(expr* e) {
    if (visited(e))
        return true;
    m_stack.push_back(sat::eframe(e));
    return false;
}

bool solver::visited(expr* e) {
    euf::enode* n = expr2enode(e);
    return n && n->is_attached_to(get_id());
}

bool solver::post_visit(expr* e, bool sign, bool root) {
    euf::enode* n = expr2enode(e);
    SASSERT(!n || !n->is_attached_to(get_id()));
    if (!n)
        n = mk_enode(e);
    mk_var(n);

    // Inject function-specific axioms
    if (!is_app(e))
        return true;
    app* a = to_app(e);
    if (a->get_family_id() != get_id())
        return true;

    switch (a->get_decl_kind()) {
    case OP_DATE_MK:
        inject_mk_axioms(a);
        break;
    case OP_DATE_ADD:
        inject_add_axioms(a);
        break;
    case OP_DATE_SUB:
        inject_sub_axioms(a);
        break;
    case OP_DATE_LT:
    case OP_DATE_LE:
    case OP_DATE_GT:
    case OP_DATE_GE:
        inject_cmp_axioms(a);
        break;
    default:
        break;
    }
    return true;
}

euf::theory_var solver::mk_var(euf::enode* n) {
    if (is_attached_to_var(n))
        return n->get_th_var(get_id());
    euf::theory_var r = th_euf_solver::mk_var(n);
    ctx.attach_th_var(n, this, r);
    return r;
}

void solver::apply_sort_cnstr(euf::enode* n, sort* s) {
    if (!m_util.is_date(s))
        return;
    inject_date_axioms(n->get_expr());
}

// ============================================================
// Concrete date arithmetic helpers
// ============================================================

int64_t solver::floor_div(int64_t a, int64_t b) {
    int64_t q = a / b;
    int64_t r = a % b;
    if (r != 0 && (r < 0) != (b < 0)) q--;
    return q;
}

int64_t solver::floor_mod(int64_t a, int64_t b) {
    return a - floor_div(a, b) * b;
}

int64_t solver::days_in_month_concrete(int64_t y, int64_t m) {
    if (m == 2) {
        bool leap = (y % 4 == 0 && y % 100 != 0) || y % 400 == 0;
        return leap ? 29 : 28;
    }
    static const int dim[] = {0,31,28,31,30,31,30,31,31,30,31,30,31};
    if (m >= 1 && m <= 12) return dim[m];
    return 30;
}

bool solver::compute_date_add(int64_t y, int64_t m, int64_t d,
                               int64_t py, int64_t pm, int64_t pd,
                               int64_t& ry, int64_t& rm, int64_t& rd) {
    int64_t raw_month = m + 12 * py + pm;
    int64_t t  = raw_month - 1;
    int64_t y1 = y + floor_div(t, 12);
    int64_t m1 = floor_mod(t, 12) + 1;
    int64_t dim1  = days_in_month_concrete(y1, m1);
    int64_t c_day = d < dim1 ? d : dim1;
    int64_t tmp = c_day + pd;
    ry = y1; rm = m1;
    while (tmp > days_in_month_concrete(ry, rm)) {
        tmp -= days_in_month_concrete(ry, rm);
        rm++;
        if (rm == 13) { rm = 1; ry++; }
    }
    while (tmp < 1) {
        rm--;
        if (rm == 0) { rm = 12; ry--; }
        tmp += days_in_month_concrete(ry, rm);
    }
    rd = tmp;
    return true;
}

// ============================================================
// Expression builders
// ============================================================

expr_ref solver::mk_is_leap(expr* y) {
    expr* zero    = m_autil.mk_int(0);
    expr* four    = m_autil.mk_int(4);
    expr* hundred = m_autil.mk_int(100);
    expr* fourhun = m_autil.mk_int(400);
    expr* y_mod_4   = m_autil.mk_mod(y, four);
    expr* y_mod_100 = m_autil.mk_mod(y, hundred);
    expr* y_mod_400 = m_autil.mk_mod(y, fourhun);
    expr* div4   = m.mk_eq(y_mod_4, zero);
    expr* not100 = m.mk_not(m.mk_eq(y_mod_100, zero));
    expr* div400 = m.mk_eq(y_mod_400, zero);
    return expr_ref(m.mk_or(m.mk_and(div4, not100), div400), m);
}

expr_ref solver::mk_days_in_month(expr* y, expr* mo) {
    auto mk_eq_m = [&](int v) -> expr* { return m.mk_eq(mo, m_autil.mk_int(v)); };
    expr* is_31day = m.mk_or(mk_eq_m(1), m.mk_or(mk_eq_m(3), m.mk_or(mk_eq_m(5),
                     m.mk_or(mk_eq_m(7), m.mk_or(mk_eq_m(8), m.mk_or(mk_eq_m(10),
                     mk_eq_m(12)))))));
    expr* is_30day = m.mk_or(mk_eq_m(4), m.mk_or(mk_eq_m(6), m.mk_or(mk_eq_m(9),
                     mk_eq_m(11))));
    expr* is_feb  = mk_eq_m(2);
    expr_ref is_leap_ref = mk_is_leap(y);  // keep alive so raw pointer is valid
    expr* is_leap = is_leap_ref.get();
    expr* feb_days = m.mk_ite(is_leap, m_autil.mk_int(29), m_autil.mk_int(28));
    return expr_ref(
        m.mk_ite(is_31day, m_autil.mk_int(31),
            m.mk_ite(is_30day, m_autil.mk_int(30),
                m.mk_ite(is_feb, feb_days, m_autil.mk_int(28)))), m);
}

expr_ref solver::mk_lex_lt(expr* d1, expr* d2) {
    expr* y1  = m_util.mk_year(d1);
    expr* m1  = m_util.mk_month(d1);
    expr* da1 = m_util.mk_day(d1);
    expr* y2  = m_util.mk_year(d2);
    expr* m2  = m_util.mk_month(d2);
    expr* da2 = m_util.mk_day(d2);
    // Note: use not(b <= a) for a < b to avoid OP_LT in old core
    // In new core we can use mk_lt directly, but keep consistent
    expr* year_lt  = m.mk_not(m_autil.mk_le(y2, y1));
    expr* month_lt = m.mk_and(m.mk_eq(y1, y2), m.mk_not(m_autil.mk_le(m2, m1)));
    expr* day_lt   = m.mk_and(m.mk_eq(y1, y2),
                        m.mk_and(m.mk_eq(m1, m2), m.mk_not(m_autil.mk_le(da2, da1))));
    return expr_ref(m.mk_or(year_lt, m.mk_or(month_lt, day_lt)), m);
}

// ============================================================
// Axiom injection helpers
// ============================================================

void solver::assert_eq(expr* a, expr* b) {
    sat::literal lit = eq_internalize(a, b);
    add_unit(lit);
}

void solver::assert_formula(expr* f) {
    sat::literal lit = mk_literal(f);
    add_unit(lit);
}

void solver::inject_date_axioms(expr* e) {
    // Skip explicit constructors: selector axioms suffice; avoids infinite recursion
    if (m_util.is_date_mk(e))
        return;

    if (m_processed.contains(e))
        return;
    m_processed.insert(e);

    expr* mo = m_util.mk_month(e);
    expr* da = m_util.mk_day(e);
    expr* yr = m_util.mk_year(e);

    // 1 ≤ month(e) ≤ 12
    assert_formula(m_autil.mk_ge(mo, m_autil.mk_int(1)));
    assert_formula(m_autil.mk_le(mo, m_autil.mk_int(12)));

    // 1 ≤ day(e) ≤ days_in_month(year(e), month(e))
    assert_formula(m_autil.mk_ge(da, m_autil.mk_int(1)));
    expr_ref dim = mk_days_in_month(yr, mo);
    assert_formula(m_autil.mk_le(da, dim.get()));

    // Reconstruction: e = date.mk(year(e), month(e), day(e))
    expr* mk_e = m_util.mk_date(yr, mo, da);
    assert_eq(e, mk_e);
}

void solver::inject_mk_axioms(app* mk_term) {
    expr* y  = mk_term->get_arg(0);
    expr* mo = mk_term->get_arg(1);
    expr* da = mk_term->get_arg(2);
    assert_eq(m_util.mk_year(mk_term), y);
    assert_eq(m_util.mk_month(mk_term), mo);
    assert_eq(m_util.mk_day(mk_term), da);
}

void solver::inject_cmp_axioms(app* atom) {
    decl_kind k = atom->get_decl_kind();
    expr* d1 = atom->get_arg(0);
    expr* d2 = atom->get_arg(1);

    expr_ref lex_lt  = mk_lex_lt(d1, d2);
    expr_ref lex_lt2 = mk_lex_lt(d2, d1);
    expr* eq12 = m.mk_eq(d1, d2);

    expr* rhs = nullptr;
    switch (k) {
    case OP_DATE_LT: rhs = lex_lt.get(); break;
    case OP_DATE_LE: rhs = m.mk_or(lex_lt.get(), eq12); break;
    case OP_DATE_GT: rhs = lex_lt2.get(); break;
    case OP_DATE_GE: rhs = m.mk_or(lex_lt2.get(), eq12); break;
    default: return;
    }

    assert_formula(m.mk_iff(atom, rhs));
}

void solver::inject_add_axioms(app* add_term) {
    expr* base = add_term->get_arg(0);
    expr* py_e = add_term->get_arg(1);
    expr* pm_e = add_term->get_arg(2);
    expr* pd_e = add_term->get_arg(3);

    rational py_r, pm_r, pd_r;
    bool py_concrete = m_autil.is_numeral(py_e, py_r) && py_r.is_int();
    bool pm_concrete = m_autil.is_numeral(pm_e, pm_r) && pm_r.is_int();
    bool pd_concrete = m_autil.is_numeral(pd_e, pd_r) && pd_r.is_int();

    bool base_is_concrete_mk = false;
    int64_t base_y = 0, base_m = 0, base_d = 0;
    if (m_util.is_date_mk(base) && py_concrete && pm_concrete && pd_concrete) {
        app* mk = to_app(base);
        rational y_r, m_r, d_r;
        if (m_autil.is_numeral(mk->get_arg(0), y_r) && y_r.is_int() &&
            m_autil.is_numeral(mk->get_arg(1), m_r) && m_r.is_int() &&
            m_autil.is_numeral(mk->get_arg(2), d_r) && d_r.is_int()) {
            base_is_concrete_mk = true;
            base_y = (int64_t)y_r.get_int64();
            base_m = (int64_t)m_r.get_int64();
            base_d = (int64_t)d_r.get_int64();
        }
    }

    if (base_is_concrete_mk) {
        int64_t ry, rm, rd;
        int64_t ipy = (int64_t)py_r.get_int64();
        int64_t ipm = (int64_t)pm_r.get_int64();
        int64_t ipd = (int64_t)pd_r.get_int64();
        compute_date_add(base_y, base_m, base_d, ipy, ipm, ipd, ry, rm, rd);
        expr* result_mk = m_util.mk_date(m_autil.mk_int((int)ry), m_autil.mk_int((int)rm), m_autil.mk_int((int)rd));
        assert_eq(add_term, result_mk);
        return;
    }

    if (py_concrete && pm_concrete && pd_concrete) {
        int64_t ipy = (int64_t)py_r.get_int64();
        int64_t ipm = (int64_t)pm_r.get_int64();
        int64_t ipd = (int64_t)pd_r.get_int64();

        if (ipy == 0 && ipm == 0 && ipd == 0) {
            // Direct equality: date.add(d, 0, 0, 0) = d
            assert_eq(add_term, base);
            return;
        }

        if (ipy == 0 && ipm == 0) {
            if (ipd > 0)
                assert_formula(m_util.mk_lt(base, add_term));
            else if (ipd < 0)
                assert_formula(m_util.mk_lt(add_term, base));
            else {
                assert_eq(add_term, base);
            }
            return;
        }

        // General case with non-zero py or pm
        expr* yd = m_util.mk_year(base);
        expr* md = m_util.mk_month(base);
        expr* dd = m_util.mk_day(base);

        int64_t month_offset = 12 * ipy + ipm;
        expr* raw_m_expr = m_autil.mk_add(md, m_autil.mk_int((int)month_offset));
        expr* t_expr = m_autil.mk_sub(raw_m_expr, m_autil.mk_int(1));
        expr* y1 = m_autil.mk_add(yd, m_autil.mk_idiv(t_expr, m_autil.mk_int(12)));
        expr* m1 = m_autil.mk_add(m_autil.mk_mod(t_expr, m_autil.mk_int(12)), m_autil.mk_int(1));

        expr_ref dim1 = mk_days_in_month(y1, m1);
        expr* clamp = m.mk_ite(m_autil.mk_le(dd, dim1.get()), dd, dim1.get());

        if (ipd == 0) {
            assert_eq(m_util.mk_year(add_term), y1);
            assert_eq(m_util.mk_month(add_term), m1);
            assert_eq(m_util.mk_day(add_term), clamp);
        } else if (ipd > 0) {
            assert_formula(m_util.mk_lt(base, add_term));
        } else {
            assert_formula(m_util.mk_lt(add_term, base));
        }
    }
}

void solver::inject_sub_axioms(app* sub_term) {
    expr* base = sub_term->get_arg(0);
    expr* py_e = sub_term->get_arg(1);
    expr* pm_e = sub_term->get_arg(2);
    expr* pd_e = sub_term->get_arg(3);

    // Negate offsets: use concrete literals so inject_add_axioms can detect them
    rational py_r, pm_r, pd_r;
    expr* neg_py = (m_autil.is_numeral(py_e, py_r) && py_r.is_int())
                       ? (expr*)m_autil.mk_numeral(-py_r, true) : m_autil.mk_uminus(py_e);
    expr* neg_pm = (m_autil.is_numeral(pm_e, pm_r) && pm_r.is_int())
                       ? (expr*)m_autil.mk_numeral(-pm_r, true) : m_autil.mk_uminus(pm_e);
    expr* neg_pd = (m_autil.is_numeral(pd_e, pd_r) && pd_r.is_int())
                       ? (expr*)m_autil.mk_numeral(-pd_r, true) : m_autil.mk_uminus(pd_e);

    expr* equiv_add = m_util.mk_add(base, neg_py, neg_pm, neg_pd);
    assert_eq(sub_term, equiv_add);
}

// ============================================================
// Model building
// ============================================================

void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
    expr* e = n->get_expr();

    if (!m_util.is_date(e->get_sort()))
        return;

    // Find the year, month, day values from the model
    expr_ref yr_val(m), mo_val(m), da_val(m);

    app* yr_expr = m_util.mk_year(e);
    app* mo_expr = m_util.mk_month(e);
    app* da_expr = m_util.mk_day(e);

    euf::enode* yr_node = expr2enode(yr_expr);
    euf::enode* mo_node = expr2enode(mo_expr);
    euf::enode* da_node = expr2enode(da_expr);

    if (yr_node) yr_val = values.get(yr_node->get_root()->get_id());
    if (mo_node) mo_val = values.get(mo_node->get_root()->get_id());
    if (da_node) da_val = values.get(da_node->get_root()->get_id());

    if (!yr_val) yr_val = m_autil.mk_int(0);
    if (!mo_val) mo_val = m_autil.mk_int(1);
    if (!da_val) da_val = m_autil.mk_int(1);

    values.set(n->get_id(), m_util.mk_date(yr_val, mo_val, da_val));
}

bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
    expr* e = n->get_expr();
    if (!m_util.is_date(e->get_sort()))
        return false;

    // Date values depend on their year/month/day enodes
    app* yr_expr = m_util.mk_year(e);
    app* mo_expr = m_util.mk_month(e);
    app* da_expr = m_util.mk_day(e);

    for (app* sub : {yr_expr, mo_expr, da_expr}) {
        euf::enode* sub_node = expr2enode(sub);
        if (sub_node)
            dep.add(n, sub_node->get_root());
    }
    return true;
}

bool solver::include_func_interp(func_decl* f) const {
    return false;
}

} // namespace date
