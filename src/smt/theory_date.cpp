/*++
Copyright (c) 2026 CMU PASTA Lab

Module Name:

    theory_date.cpp

Abstract:

    Implementation of the Date theory for the legacy SMT core.

    Axiom injection strategy:
      1. apply_sort_cnstr: inject validity + reconstruction for Date terms
      2. internalize_term:
           date.mk       -> selector axioms
           date.add      -> arithmetic axioms
           date.sub      -> reduction to date.add
           date.year/month/day -> create enode only
      3. internalize_atom:
           date.lt/le/gt/ge -> comparison expansion

Author:

    Angel Cui

--*/

#include "smt/smt_context.h"
#include "smt/theory_date.h"

namespace smt {

// ============================================================
// Construction
// ============================================================

theory_date::theory_date(context& ctx, ast_manager& m)
    : theory(ctx, m.mk_family_id("date")),
      m_util(m),
      m_autil(m)
{}

theory* theory_date::mk_fresh(context* new_ctx) {
    return alloc(theory_date, *new_ctx, new_ctx->get_manager());
}

void theory_date::reset_eh() {
    m_processed.reset();
    theory::reset_eh();
}

final_check_status theory_date::final_check_eh(unsigned) {
    return FC_DONE;
}

// ============================================================
// Internalization
// ============================================================

bool theory_date::internalize_atom(app* atom, bool gate_ctx) {
    return internalize_term(atom);
}

bool theory_date::internalize_term(app* term) {
    if (ctx.e_internalized(term))
        return true;

    // Internalize all arguments first
    for (unsigned i = 0; i < term->get_num_args(); ++i)
        ctx.internalize(term->get_arg(i), false);

    // Check again (argument internalization might have done this term)
    if (ctx.e_internalized(term))
        return true;

    bool is_bool = m.is_bool(term);
    enode* e = ctx.mk_enode(term, false, is_bool, true);

    if (is_bool) {
        bool_var bv = ctx.mk_bool_var(term);
        ctx.set_var_theory(bv, get_id());
        ctx.set_enode_flag(bv, true);
    }

    // Now inject function-specific axioms
    decl_kind k = term->get_decl_kind();
    if (term->get_family_id() == get_family_id()) {
        switch (k) {
        case OP_DATE_MK:
            inject_mk_axioms(term);
            break;
        case OP_DATE_ADD:
            inject_add_axioms(term);
            break;
        case OP_DATE_SUB:
            inject_sub_axioms(term);
            break;
        case OP_DATE_LT:
        case OP_DATE_LE:
        case OP_DATE_GT:
        case OP_DATE_GE:
            inject_cmp_axioms(term);
            break;
        default:
            break;
        }
    }

    return true;
}

void theory_date::apply_sort_cnstr(enode* n, sort* s) {
    if (!m_util.is_date(s))
        return;
    if (is_attached_to_var(n))
        return;
    mk_var(n);
    inject_date_axioms(n->get_expr());
}

// ============================================================
// Concrete date arithmetic helpers
// ============================================================

int64_t theory_date::floor_div(int64_t a, int64_t b) {
    int64_t q = a / b;
    int64_t r = a % b;
    if (r != 0 && (r < 0) != (b < 0)) q--;
    return q;
}

int64_t theory_date::floor_mod(int64_t a, int64_t b) {
    return a - floor_div(a, b) * b;
}

int64_t theory_date::days_in_month_concrete(int64_t y, int64_t m) {
    if (m == 2) {
        bool leap = (y % 4 == 0 && y % 100 != 0) || y % 400 == 0;
        return leap ? 29 : 28;
    }
    static const int dim[] = {0,31,28,31,30,31,30,31,31,30,31,30,31};
    if (m >= 1 && m <= 12) return dim[m];
    return 30; // unreachable for valid months
}

bool theory_date::compute_date_add(int64_t y, int64_t m, int64_t d,
                                    int64_t py, int64_t pm, int64_t pd,
                                    int64_t& ry, int64_t& rm, int64_t& rd) {
    // Step 1: month normalization
    int64_t raw_month = m + 12 * py + pm;
    int64_t t  = raw_month - 1;
    int64_t y1 = y + floor_div(t, 12);
    int64_t m1 = floor_mod(t, 12) + 1;

    // Step 2: end-of-month clamp
    int64_t dim1   = days_in_month_concrete(y1, m1);
    int64_t c_day  = d < dim1 ? d : dim1;

    // Step 3: day carry
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

expr_ref theory_date::mk_is_leap(expr* y) {
    // is_leap(y) = (y%4=0 ∧ y%100≠0) ∨ y%400=0
    arith_util& a = m_util.arith();
    expr* zero    = a.mk_int(0);
    expr* four    = a.mk_int(4);
    expr* hundred = a.mk_int(100);
    expr* fourhun = a.mk_int(400);

    expr* y_mod_4   = a.mk_mod(y, four);
    expr* y_mod_100 = a.mk_mod(y, hundred);
    expr* y_mod_400 = a.mk_mod(y, fourhun);

    expr* div4    = m.mk_eq(y_mod_4, zero);
    expr* not100  = m.mk_not(m.mk_eq(y_mod_100, zero));
    expr* div400  = m.mk_eq(y_mod_400, zero);

    return expr_ref(m.mk_or(m.mk_and(div4, not100), div400), m);
}

expr_ref theory_date::mk_days_in_month(expr* y, expr* mo) {
    // days_in_month(y, m) as an ite expression
    arith_util& a = m_util.arith();
    auto mk_eq_m = [&](int v) -> expr* { return m.mk_eq(mo, a.mk_int(v)); };

    expr* is_31day = m.mk_or(mk_eq_m(1), m.mk_or(mk_eq_m(3), m.mk_or(mk_eq_m(5),
                     m.mk_or(mk_eq_m(7), m.mk_or(mk_eq_m(8), m.mk_or(mk_eq_m(10),
                     mk_eq_m(12)))))));

    expr* is_30day = m.mk_or(mk_eq_m(4), m.mk_or(mk_eq_m(6), m.mk_or(mk_eq_m(9),
                     mk_eq_m(11))));

    expr* is_feb  = mk_eq_m(2);
    expr_ref is_leap_ref = mk_is_leap(y);  // keep alive so raw pointer is valid
    expr* is_leap = is_leap_ref.get();

    expr* feb_days = m.mk_ite(is_leap, a.mk_int(29), a.mk_int(28));

    return expr_ref(
        m.mk_ite(is_31day, a.mk_int(31),
            m.mk_ite(is_30day, a.mk_int(30),
                m.mk_ite(is_feb, feb_days, a.mk_int(28)))), m);
}

// Linear date score for comparison: score(d) = K*year(d) + L*month(d) + day(d)
// With K=385, L=32: K > 12*L+31=384, so this preserves lex order for valid dates.
// Crucially: no ITE or IDIV — pure linear arithmetic, LP-friendly.
expr_ref theory_date::mk_abs_day(expr* d) {
    arith_util& a = m_util.arith();
    expr* y  = m_util.mk_year(d);
    expr* mo = m_util.mk_month(d);
    expr* da = m_util.mk_day(d);
    // score = 385*year + 32*month + day
    return expr_ref(
        a.mk_add(a.mk_mul(a.mk_int(385), y),
            a.mk_add(a.mk_mul(a.mk_int(32), mo), da)), m);
}

expr_ref theory_date::mk_lex_lt(expr* d1, expr* d2) {
    // date.lt(d1, d2) ↔ lex order on (year, month, day)
    arith_util& a = m_util.arith();
    expr* y1  = m_util.mk_year(d1);
    expr* m1  = m_util.mk_month(d1);
    expr* da1 = m_util.mk_day(d1);
    expr* y2  = m_util.mk_year(d2);
    expr* m2  = m_util.mk_month(d2);
    expr* da2 = m_util.mk_day(d2);

    // y1 < y2
    expr* year_lt = m.mk_not(a.mk_le(y2, y1));
    // y1 = y2 ∧ m1 < m2
    expr* month_lt = m.mk_and(m.mk_eq(y1, y2), m.mk_not(a.mk_le(m2, m1)));
    // y1 = y2 ∧ m1 = m2 ∧ d1 < d2
    expr* day_lt = m.mk_and(m.mk_eq(y1, y2),
                       m.mk_and(m.mk_eq(m1, m2), m.mk_not(a.mk_le(da2, da1))));

    return expr_ref(m.mk_or(year_lt, m.mk_or(month_lt, day_lt)), m);
}

// ============================================================
// Axiom injection helpers
// ============================================================

void theory_date::assert_unit(expr* formula) {
    ctx.internalize(formula, false);
    literal lit = ctx.get_literal(formula);
    ctx.mark_as_relevant(lit);
    ctx.mk_th_axiom(get_id(), 1, &lit);
}

void theory_date::inject_date_axioms(expr* e) {
    // For explicit date.mk constructors, no reconstruction/validity needed
    // here — their selector axioms (injected in inject_mk_axioms) are sufficient.
    // Also avoids infinite recursion: reconstruction of date.mk(y,m,d) would
    // create date.mk(year(date.mk(y,m,d)), ...) which would recurse.
    if (m_util.is_date_mk(e))
        return;

    if (m_processed.contains(e))
        return;
    m_processed.insert(e);

    arith_util& a = m_util.arith();
    expr* mo = m_util.mk_month(e);
    expr* da = m_util.mk_day(e);
    expr* yr = m_util.mk_year(e);

    // 1 ≤ month(e) ≤ 12
    assert_unit(a.mk_ge(mo, a.mk_int(1)));
    assert_unit(a.mk_le(mo, a.mk_int(12)));

    // 1 ≤ day(e) ≤ days_in_month(year(e), month(e))
    assert_unit(a.mk_ge(da, a.mk_int(1)));
    expr_ref dim = mk_days_in_month(yr, mo);
    assert_unit(a.mk_le(da, dim.get()));

    // Reconstruction: e = date.mk(year(e), month(e), day(e))
    expr* mk_e = m_util.mk_date(yr, mo, da);
    assert_unit(m.mk_eq(e, mk_e));
}

void theory_date::inject_mk_axioms(app* mk_term) {
    // date.year(date.mk(y,m,d)) = y
    // date.month(date.mk(y,m,d)) = m
    // date.day(date.mk(y,m,d)) = d
    expr* y  = mk_term->get_arg(0);
    expr* mo = mk_term->get_arg(1);
    expr* da = mk_term->get_arg(2);

    assert_unit(m.mk_eq(m_util.mk_year(mk_term), y));
    assert_unit(m.mk_eq(m_util.mk_month(mk_term), mo));
    assert_unit(m.mk_eq(m_util.mk_day(mk_term), da));
}

void theory_date::inject_cmp_axioms(app* atom) {
    decl_kind k = atom->get_decl_kind();
    expr* d1 = atom->get_arg(0);
    expr* d2 = atom->get_arg(1);

    // Use linear score for comparison:
    // score(d) = 385*year(d) + 32*month(d) + day(d)
    // This is a pure linear formula compatible with lex order on valid dates.
    arith_util& a = m_util.arith();
    expr_ref abs1 = mk_abs_day(d1);
    expr_ref abs2 = mk_abs_day(d2);

    // score1 < score2: ¬(score2 ≤ score1)
    expr* score_lt12 = m.mk_not(a.mk_le(abs2.get(), abs1.get()));
    // score1 ≤ score2
    expr* score_le12 = a.mk_le(abs1.get(), abs2.get());
    // score1 = score2
    expr* score_eq12 = m.mk_eq(abs1.get(), abs2.get());
    // score1 > score2: ¬(score1 ≤ score2)
    expr* score_gt12 = m.mk_not(a.mk_le(abs1.get(), abs2.get()));
    // score1 ≥ score2
    expr* score_ge12 = a.mk_le(abs2.get(), abs1.get());

    expr* rhs = nullptr;
    expr* rhs_backward = nullptr;
    switch (k) {
    case OP_DATE_LT:
        rhs = score_lt12;
        rhs_backward = score_lt12;  // same for strict lt
        break;
    case OP_DATE_LE:
        rhs = score_le12;
        rhs_backward = score_le12;
        break;
    case OP_DATE_GT:
        rhs = score_gt12;
        rhs_backward = score_gt12;
        break;
    case OP_DATE_GE:
        rhs = score_ge12;
        rhs_backward = score_ge12;
        break;
    default:
        return;
    }

    // Inject both directions as explicit 2-literal clauses for BCP efficiency:
    // Forward:  {~atom, rhs}  (if atom then rhs)
    // Backward: {atom, ~rhs}  (if rhs then atom)
    literal atom_lit = mk_literal(atom);
    literal rhs_lit  = mk_literal(rhs);

    // Forward: if atom then score_comparison
    literal fwd[2] = { ~atom_lit, rhs_lit };
    ctx.mk_th_axiom(get_id(), 2, fwd);

    // Backward: if score_comparison then atom
    literal bwd[2] = { atom_lit, ~rhs_lit };
    ctx.mk_th_axiom(get_id(), 2, bwd);
}

void theory_date::inject_add_axioms(app* add_term) {
    expr* base = add_term->get_arg(0);
    expr* py_e = add_term->get_arg(1);
    expr* pm_e = add_term->get_arg(2);
    expr* pd_e = add_term->get_arg(3);

    arith_util& a = m_util.arith();

    // Try to get concrete py, pm, pd values
    rational py_r, pm_r, pd_r;
    bool py_concrete = a.is_numeral(py_e, py_r) && py_r.is_int();
    bool pm_concrete = a.is_numeral(pm_e, pm_r) && pm_r.is_int();
    bool pd_concrete = a.is_numeral(pd_e, pd_r) && pd_r.is_int();

    // Check if base is a concrete date.mk
    bool base_is_concrete_mk = false;
    int64_t base_y = 0, base_m = 0, base_d = 0;
    if (m_util.is_date_mk(base) && py_concrete && pm_concrete && pd_concrete) {
        app* mk = to_app(base);
        rational y_r, m_r, d_r;
        if (a.is_numeral(mk->get_arg(0), y_r) && y_r.is_int() &&
            a.is_numeral(mk->get_arg(1), m_r) && m_r.is_int() &&
            a.is_numeral(mk->get_arg(2), d_r) && d_r.is_int()) {
            base_is_concrete_mk = true;
            base_y = (int64_t)y_r.get_int64();
            base_m = (int64_t)m_r.get_int64();
            base_d = (int64_t)d_r.get_int64();
        }
    }

    if (base_is_concrete_mk) {
        // Evaluate the result directly
        int64_t ry, rm, rd;
        int64_t ipy = (int64_t)py_r.get_int64();
        int64_t ipm = (int64_t)pm_r.get_int64();
        int64_t ipd = (int64_t)pd_r.get_int64();
        compute_date_add(base_y, base_m, base_d, ipy, ipm, ipd, ry, rm, rd);
        expr* result_mk = m_util.mk_date(a.mk_int((int)ry), a.mk_int((int)rm), a.mk_int((int)rd));
        // add_term = date.mk(ry, rm, rd)
        assert_unit(m.mk_eq(add_term, result_mk));
        return;
    }

    // Symbolic base: handle by cases on py, pm, pd
    if (py_concrete && pm_concrete && pd_concrete) {
        int64_t ipy = (int64_t)py_r.get_int64();
        int64_t ipm = (int64_t)pm_r.get_int64();
        int64_t ipd = (int64_t)pd_r.get_int64();

        if (ipy == 0 && ipm == 0 && ipd == 0) {
            // Direct equality: date.add(d, 0, 0, 0) = d
            assert_unit(m.mk_eq(add_term, base));
            return;
        }

        if (ipy == 0 && ipm == 0) {
            // Pure day offset
            if (ipd > 0) {
                // date.add(d, 0, 0, n) > d for n > 0
                assert_unit(m_util.mk_lt(base, add_term));
            } else if (ipd < 0) {
                // date.add(d, 0, 0, n) < d for n < 0
                assert_unit(m_util.mk_lt(add_term, base));
            } else {
                // pd = 0 already handled above
                assert_unit(m.mk_eq(m_util.mk_year(add_term), m_util.mk_year(base)));
                assert_unit(m.mk_eq(m_util.mk_month(add_term), m_util.mk_month(base)));
                assert_unit(m.mk_eq(m_util.mk_day(add_term), m_util.mk_day(base)));
            }
            return;
        }

        // General case with symbolic base and concrete py/pm/pd:
        // Use the three-step algorithm expressed in Z3 arithmetic
        expr* yd = m_util.mk_year(base);
        expr* md = m_util.mk_month(base);
        expr* dd = m_util.mk_day(base);

        // Step 1: month normalization
        // raw_month = md + 12*py + pm
        // t = raw_month - 1
        // y1 = yd + (t div 12)  [floor div with positive divisor 12]
        // m1 = (t mod 12) + 1   [floor mod, result in [1..12]]
        int64_t month_offset = 12 * ipy + ipm; // py*12 + pm as concrete integer
        expr* raw_m_expr = a.mk_add(md, a.mk_int((int)month_offset));
        expr* t_expr = a.mk_sub(raw_m_expr, a.mk_int(1));
        expr* y1 = a.mk_add(yd, a.mk_idiv(t_expr, a.mk_int(12)));
        expr* m1 = a.mk_add(a.mk_mod(t_expr, a.mk_int(12)), a.mk_int(1));

        // Step 2: EOM clamp
        expr_ref dim1 = mk_days_in_month(y1, m1);
        // clamp_day = min(dd, dim1) = ite(dd <= dim1, dd, dim1)
        expr* clamp = m.mk_ite(a.mk_le(dd, dim1.get()), dd, dim1.get());

        // Step 3: day carry
        // tmp = clamp + pd
        expr* tmp = a.mk_add(clamp, a.mk_int((int)ipd));

        // The result (ry, rm, rd) satisfies:
        // 1 ≤ rm ≤ 12, 1 ≤ rd ≤ days_in_month(ry, rm)
        // and same abs_day as (y1, m1, clamp) + pd
        //
        // For pd = 0: result is (y1, m1, clamp) directly
        // For non-zero pd: assert ordering axioms
        if (ipd == 0) {
            // No day carry: result is exactly (y1, m1, clamp)
            assert_unit(m.mk_eq(m_util.mk_year(add_term), y1));
            assert_unit(m.mk_eq(m_util.mk_month(add_term), m1));
            assert_unit(m.mk_eq(m_util.mk_day(add_term), clamp));
        } else if (ipd > 0) {
            // Adding days: result is later than the intermediate date
            // But we can also assert the abs_day relationship
            // For simplicity: assert date.lt(base, result) and validity
            assert_unit(m_util.mk_lt(base, add_term));
        } else {
            // ipd < 0
            assert_unit(m_util.mk_lt(add_term, base));
        }
    }
    // For fully symbolic py/pm/pd: just validity (injected via apply_sort_cnstr)
}

void theory_date::inject_sub_axioms(app* sub_term) {
    // date.sub(d, py, pm, pd) = date.add(d, -py, -pm, -pd)
    arith_util& a = m_util.arith();
    expr* base = sub_term->get_arg(0);
    expr* py_e = sub_term->get_arg(1);
    expr* pm_e = sub_term->get_arg(2);
    expr* pd_e = sub_term->get_arg(3);

    // Negate the offsets: use concrete literals so inject_add_axioms can detect them
    rational py_r, pm_r, pd_r;
    expr* neg_py = (a.is_numeral(py_e, py_r) && py_r.is_int())
                       ? (expr*)a.mk_numeral(-py_r, true) : a.mk_uminus(py_e);
    expr* neg_pm = (a.is_numeral(pm_e, pm_r) && pm_r.is_int())
                       ? (expr*)a.mk_numeral(-pm_r, true) : a.mk_uminus(pm_e);
    expr* neg_pd = (a.is_numeral(pd_e, pd_r) && pd_r.is_int())
                       ? (expr*)a.mk_numeral(-pd_r, true) : a.mk_uminus(pd_e);

    expr* equiv_add = m_util.mk_add(base, neg_py, neg_pm, neg_pd);
    assert_unit(m.mk_eq(sub_term, equiv_add));

    // Also directly inject ordering for pure day subtraction (py=pm=0, pd>0):
    // date.sub(d, 0, 0, pd) < d when pd > 0
    bool py_zero = (a.is_numeral(py_e, py_r) && py_r.is_zero());
    bool pm_zero = (a.is_numeral(pm_e, pm_r) && pm_r.is_zero());
    if (py_zero && pm_zero &&
        a.is_numeral(pd_e, pd_r) && pd_r.is_int() && pd_r > rational(0)) {
        // Directly assert score(sub) < score(base) to avoid going through
        // the biconditional chain which requires E-graph equalities
        arith_util& a2 = m_util.arith();
        expr_ref score_sub = mk_abs_day(sub_term);
        expr_ref score_base = mk_abs_day(base);
        // score(sub) < score(base): ¬(score(base) ≤ score(sub))
        assert_unit(m.mk_not(a2.mk_le(score_base.get(), score_sub.get())));
    }
}

} // namespace smt
