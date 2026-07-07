/*++
Copyright (c) 2026 Theoria

Module Name:

    date_rewriter.h

Abstract:

    Rewriting/decision rules for the theory of calendar dates.

    The theory of dates is decided by a sound and complete reduction to
    linear integer arithmetic (with div/mod by constants). The intended
    interpretation of sort Date is the integers, where n : Int denotes the
    calendar day that lies n days after 1970-01-01 in the proleptic
    Gregorian calendar; date.to_days / date.from_days are the two
    directions of this bijection.

    Every date operation is eliminated by rewriting:

      (date.mk y m d)        -> (date.from_days <days-from-civil y m d>)
      (date.add_days t n)    -> (date.from_days (+ (date.to_days t) n))
      (date.year t)          -> <civil-year   (date.to_days t)>
      (date.month t)         -> <civil-month  (date.to_days t)>
      (date.day t)           -> <civil-day    (date.to_days t)>
      (date.dow t)           -> (+ (mod (+ (date.to_days t) 3) 7) 1)
      (date.sub t1 t2)       -> (- (date.to_days t1) (date.to_days t2))
      (date.lt t1 t2)        -> (< (date.to_days t1) (date.to_days t2))
      (date.le t1 t2)        -> (<= (date.to_days t1) (date.to_days t2))
      (date.valid y m d)     -> <month/day range constraints>
      (date.leap_year y)     -> <Gregorian leap year rule>
      (date.to_days (date.from_days x)) -> x
      (date.to_days (ite c t e)) -> (ite c (date.to_days t) (date.to_days e))
      (= t1 t2), (distinct t1 ... tn) over Date
                             -> same over the (date.to_days _) images
                                [sound and complete: to_days is a bijection]

    The days-from-civil and civil-from-days formulas follow Howard
    Hinnant's chrono algorithms; SMT-LIB div/mod by a positive constant is
    floor-based, which is exactly what the algorithms require, so the
    formulas are correct for the full (unbounded) proleptic calendar.

    After rewriting, terms of sort Date occur only as arguments of
    date.to_days or below (date.from_days _). The remaining "foreign"
    Date-sorted terms are uninterpreted constants (and applications of
    uninterpreted functions with Date-free domains), which is a sound
    residue because every Date equality/observation has been mapped
    through the bijection. Constructions that would escape this fragment
    (uninterpreted functions taking Date arguments, arrays/sequences/
    datatypes over Date, quantification over Date) are rejected with an
    error in th_rewriter rather than risking an unsound answer.

Author:

    Claude (Theoria date theory) 2026-07-07

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"

class date_rewriter {
    ast_manager & m;
    date_util     m_util;
    arith_util    m_arith;

    expr * mk_days_from_civil(expr * y, expr * mo, expr * d);
    expr * mk_idiv(expr * x, int c);
    expr * mk_mod(expr * x, int c);
    expr * mk_mul(int c, expr * x);
    expr * mk_leap_year(expr * y);

    // pieces of the civil-from-days computation, all over z = days since epoch
    void mk_civil_parts(expr * z, expr_ref & mp, expr_ref & doy, expr_ref & yoe_plus_era400);

public:
    date_rewriter(ast_manager & m):m(m), m_util(m), m_arith(m) {}

    family_id get_fid() const { return m_util.get_family_id(); }
    date_util & u() { return m_util; }

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    // equality / distinct over sort Date
    br_status mk_eq_core(expr * a, expr * b, expr_ref & result);
    br_status mk_distinct_core(unsigned num_args, expr * const * args, expr_ref & result);
};
