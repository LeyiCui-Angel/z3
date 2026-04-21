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

    // Enforce component validity so that date.mk(y, m, d) only produces
    // calendar-valid dates.  inject_date_axioms skips explicit constructors
    // to avoid recursion, so we add the same constraints here directly.
    // 1 ≤ month ≤ 12
    assert_formula(m_autil.mk_ge(mo, m_autil.mk_int(1)));
    assert_formula(m_autil.mk_le(mo, m_autil.mk_int(12)));
    // 1 ≤ day ≤ days_in_month(year, month)
    assert_formula(m_autil.mk_ge(da, m_autil.mk_int(1)));
    expr_ref dim = mk_days_in_month(y, mo);
    assert_formula(m_autil.mk_le(da, dim.get()));
}

void solver::inject_cmp_axioms(app* atom) {
    decl_kind k = atom->get_decl_kind();
    expr* d1 = atom->get_arg(0);
    expr* d2 = atom->get_arg(1);

    // Normalise: ge(d1,d2) = le(d2,d1), gt(d1,d2) = lt(d2,d1)
    bool is_ge_gt = (k == OP_DATE_GE || k == OP_DATE_GT);
    bool strict   = (k == OP_DATE_LT || k == OP_DATE_GT);
    expr* lo = is_ge_gt ? d2 : d1;
    expr* hi = is_ge_gt ? d1 : d2;

    // For concrete date.mk(y,m,d) terms, use raw integer literals directly so that
    // the arithmetic solver sees e.g. "year(D8) < 2100" immediately without waiting
    // for EUF propagation of date.year(date.mk(2100,2,28)) = 2100.
    auto get_comp = [&](expr* d, expr*& y_out, expr*& m_out, expr*& da_out) {
        if (m_util.is_date_mk(d)) {
            app* mk = to_app(d);
            rational yr_r, mo_r, da_r;
            if (m_autil.is_numeral(mk->get_arg(0), yr_r) && yr_r.is_int() &&
                m_autil.is_numeral(mk->get_arg(1), mo_r) && mo_r.is_int() &&
                m_autil.is_numeral(mk->get_arg(2), da_r) && da_r.is_int()) {
                y_out  = m_autil.mk_numeral(yr_r, true);
                m_out  = m_autil.mk_numeral(mo_r, true);
                da_out = m_autil.mk_numeral(da_r, true);
                return;
            }
        }
        y_out  = m_util.mk_year(d);
        m_out  = m_util.mk_month(d);
        da_out = m_util.mk_day(d);
    };

    expr *y_lo, *m_lo, *d_lo, *y_hi, *m_hi, *d_hi;
    get_comp(lo, y_lo, m_lo, d_lo);
    get_comp(hi, y_hi, m_hi, d_hi);

    // Primitive SAT literals for arithmetic/EUF comparisons.
    // Use ¬(b ≤ a) to express a < b (avoids OP_LT atoms in arith).
    literal yr_lt  = mk_literal(m.mk_not(m_autil.mk_le(y_hi, y_lo))); // year(lo) < year(hi)
    literal yr_eq  = mk_literal(m.mk_eq(y_lo, y_hi));
    literal mo_lt  = mk_literal(m.mk_not(m_autil.mk_le(m_hi, m_lo))); // month(lo) < month(hi)
    literal mo_eq  = mk_literal(m.mk_eq(m_lo, m_hi));
    // For le: day(lo) ≤ day(hi); for lt: day(lo) < day(hi) i.e. ¬(d_hi ≤ d_lo)
    literal da_cmp = strict
        ? mk_literal(m.mk_not(m_autil.mk_le(d_hi, d_lo)))
        : mk_literal(m_autil.mk_le(d_lo, d_hi));

    literal A = mk_literal(atom);

    // Forward clauses: A (date comparison true) → lex comparison holds.
    // These are the critical clauses that enforce bounds on date variables.
    //
    // F1: A → year(lo) ≤ year(hi)            i.e. {¬A, yr_lt, yr_eq}
    add_clause(~A, yr_lt, yr_eq);
    // F2: A ∧ yr_eq → month(lo) ≤ month(hi)  i.e. {¬A, ¬yr_eq, mo_lt, mo_eq}
    add_clause(~A, ~yr_eq, mo_lt, mo_eq);
    // F3: A ∧ yr_eq ∧ mo_eq → day cmp        i.e. {¬A, ¬yr_eq, ¬mo_eq, da_cmp}
    add_clause(~A, ~yr_eq, ~mo_eq, da_cmp);

    // Backward clauses: lex comparison holds → A (date comparison true).
    // These ensure the atom is set correctly for use in disjunctions.
    //
    // B1: yr_lt → A                           i.e. {A, ¬yr_lt}
    add_clause(A, ~yr_lt);
    // B2: yr_eq ∧ mo_lt → A                  i.e. {A, ¬yr_eq, ¬mo_lt}
    add_clause(A, ~yr_eq, ~mo_lt);
    // B3: yr_eq ∧ mo_eq ∧ da_cmp → A        i.e. {A, ¬yr_eq, ¬mo_eq, ¬da_cmp}
    add_clause(A, ~yr_eq, ~mo_eq, ~da_cmp);
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

    if (py_concrete && pm_concrete && pd_concrete && m_util.is_date_mk(base)) {
        app* mk = to_app(base);
        rational y_r, m_r, d_r;
        if (m_autil.is_numeral(mk->get_arg(0), y_r) && y_r.is_int() &&
            m_autil.is_numeral(mk->get_arg(1), m_r) && m_r.is_int() &&
            m_autil.is_numeral(mk->get_arg(2), d_r) && d_r.is_int()) {
            base_is_concrete_mk = true;
            base_y = y_r.get_int64();
            base_m = m_r.get_int64();
            base_d = d_r.get_int64();
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
        int64_t month_offset = 12 * ipy + ipm;

        if (month_offset == 0 && ipd == 0) {
            // date.add(d, 0, 0, 0) = d
            assert_eq(add_term, base);
            return;
        }

        expr* yd = m_util.mk_year(base);
        expr* md = m_util.mk_month(base);
        expr* dd = m_util.mk_day(base);

        // --- Step 1: compute (y0, m0) after month adjustment and raw day ---
        // For pure-day addition (month_offset==0): no clamping needed.
        // For month adjustment: clamp day to days-in-month of the adjusted month.
        expr* y0;
        expr* m0;
        expr* raw0;
        if (month_offset == 0) {
            y0   = yd;
            m0   = md;
            raw0 = (ipd != 0) ? m_autil.mk_add(dd, m_autil.mk_int((int)ipd)) : dd;
        } else {
            expr* raw_m = m_autil.mk_add(md, m_autil.mk_int((int)month_offset));
            expr* t     = m_autil.mk_sub(raw_m, m_autil.mk_int(1));
            y0 = m_autil.mk_add(yd, m_autil.mk_idiv(t, m_autil.mk_int(12)));
            m0 = m_autil.mk_add(m_autil.mk_mod(t, m_autil.mk_int(12)), m_autil.mk_int(1));
            expr_ref dim_adj = mk_days_in_month(y0, m0);
            expr* clamp = m.mk_ite(m_autil.mk_le(dd, dim_adj.get()), dd, dim_adj.get());
            raw0 = (ipd != 0) ? m_autil.mk_add(clamp, m_autil.mk_int((int)ipd)) : clamp;
        }

        if (ipd == 0) {
            // Exact: month-only adjustment, no day overflow.
            // Assert add_term = date.mk(y0, m0, raw0) rather than three separate
            // selector equalities.  This lets EUF congruence-close across different
            // add/sub terms that happen to land on the same date.
            assert_eq(add_term, m_util.mk_date(y0, m0, raw0));
            return;
        }

        // --- Step 2: normalize raw0 into a valid date via bounded ITE carry loops ---
        // For a concrete ipd, at most ceil(|ipd|/28)+4 month-carry steps are needed.
        // Cap at 50 to handle offsets up to ~1400 days while keeping formula size manageable.
        int n_steps = (int)(std::abs(ipd) / 28) + 4;
        if (n_steps > 50) n_steps = 50;

        expr_ref ry(y0, m), rm(m0, m), rd(raw0, m);

        if (ipd > 0) {
            for (int i = 0; i < n_steps; i++) {
                expr_ref dim_i = mk_days_in_month(ry.get(), rm.get());
                // over := rd > dim_i  i.e.  NOT (rd <= dim_i)
                expr* over    = m.mk_not(m_autil.mk_le(rd.get(), dim_i.get()));
                expr* is_dec  = m.mk_eq(rm.get(), m_autil.mk_int(12));
                expr* rm_nxt  = m.mk_ite(is_dec, m_autil.mk_int(1),
                                         m_autil.mk_add(rm.get(), m_autil.mk_int(1)));
                expr* ry_nxt  = m.mk_ite(is_dec,
                                         m_autil.mk_add(ry.get(), m_autil.mk_int(1)),
                                         ry.get());
                rd = m.mk_ite(over, m_autil.mk_sub(rd.get(), dim_i.get()), rd.get());
                ry = m.mk_ite(over, ry_nxt, ry.get());
                rm = m.mk_ite(over, rm_nxt, rm.get());
            }
        } else { // ipd < 0
            for (int i = 0; i < n_steps; i++) {
                // under := rd < 1  i.e.  NOT (rd >= 1)
                expr* under   = m.mk_not(m_autil.mk_ge(rd.get(), m_autil.mk_int(1)));
                expr* is_jan  = m.mk_eq(rm.get(), m_autil.mk_int(1));
                expr* rm_prv  = m.mk_ite(is_jan, m_autil.mk_int(12),
                                         m_autil.mk_sub(rm.get(), m_autil.mk_int(1)));
                expr* ry_prv  = m.mk_ite(is_jan,
                                         m_autil.mk_sub(ry.get(), m_autil.mk_int(1)),
                                         ry.get());
                // Tentatively update (ry, rm) to the previous month, then add its length.
                expr_ref ry_t(m.mk_ite(under, ry_prv, ry.get()), m);
                expr_ref rm_t(m.mk_ite(under, rm_prv, rm.get()), m);
                expr_ref dim_prv = mk_days_in_month(ry_t.get(), rm_t.get());
                rd = m.mk_ite(under,
                              m_autil.mk_add(rd.get(), dim_prv.get()),
                              rd.get());
                ry = ry_t;
                rm = rm_t;
            }
        }

        // Assert add_term = date.mk(ry, rm, rd) rather than three separate selector
        // equalities.  The constructor equality lets EUF congruence-close across
        // different add/sub terms that land on the same date (e.g. "+1 month" and
        // "+28 days" from Feb 28 both resolve to Mar 28 → they must be equal).
        assert_eq(add_term, m_util.mk_date(ry.get(), rm.get(), rd.get()));
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

    // Case 1: date.add(base, py, pm, pd) or date.sub(base, py, pm, pd)
    // Compute the result concretely from the base's already-computed model value.
    if (is_app(e) && (m_util.is_date_add(e) || m_util.is_date_sub(e))) {
        app*  a      = to_app(e);
        bool  is_sub = m_util.is_date_sub(e);
        expr* base   = a->get_arg(0);
        expr* py_e   = a->get_arg(1);
        expr* pm_e   = a->get_arg(2);
        expr* pd_e   = a->get_arg(3);

        euf::enode* base_node = expr2enode(base);
        expr* base_val = base_node ? values.get(base_node->get_root()->get_id()) : nullptr;

        rational py_r, pm_r, pd_r;
        bool py_ok = m_autil.is_numeral(py_e, py_r) && py_r.is_int();
        bool pm_ok = m_autil.is_numeral(pm_e, pm_r) && pm_r.is_int();
        bool pd_ok = m_autil.is_numeral(pd_e, pd_r) && pd_r.is_int();

        if (base_val && m_util.is_date_mk(base_val) && py_ok && pm_ok && pd_ok) {
            app* base_mk = to_app(base_val);
            rational by_r, bm_r, bd_r;
            if (m_autil.is_numeral(base_mk->get_arg(0), by_r) && by_r.is_int() &&
                m_autil.is_numeral(base_mk->get_arg(1), bm_r) && bm_r.is_int() &&
                m_autil.is_numeral(base_mk->get_arg(2), bd_r) && bd_r.is_int()) {

                int64_t ipy = py_r.get_int64(), ipm = pm_r.get_int64(), ipd = pd_r.get_int64();
                if (is_sub) { ipy = -ipy; ipm = -ipm; ipd = -ipd; }
                int64_t ry, rm, rd;
                compute_date_add(by_r.get_int64(), bm_r.get_int64(), bd_r.get_int64(),
                                 ipy, ipm, ipd, ry, rm, rd);
                values.set(n->get_id(), m_util.mk_date(
                    m_autil.mk_int((int)ry),
                    m_autil.mk_int((int)rm),
                    m_autil.mk_int((int)rd)));
                return;
            }
        }
        // Fall through to selector-based approach if concrete eval isn't possible.
    }

    // Case 2: selector-based (for free Date variables and fallback).
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

    // date.add/date.sub must be valued after their base date.
    if (is_app(e) && (m_util.is_date_add(e) || m_util.is_date_sub(e))) {
        euf::enode* base_node = expr2enode(to_app(e)->get_arg(0));
        if (base_node)
            dep.add(n, base_node->get_root());
    }

    // Date values also depend on their year/month/day selector enodes.
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
