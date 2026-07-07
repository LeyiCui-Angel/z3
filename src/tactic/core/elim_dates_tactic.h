/*++
Copyright (c) 2026 Theoria

Module Name:

    elim_dates_tactic.h

Abstract:

    Tactic that eliminates the theory of calendar dates from a goal by
    reduction to integer arithmetic. Date operations are expanded by
    date_rewriter, and every uninterpreted Date-sorted constant c is
    replaced by (date.from_days k_c) for a fresh integer constant k_c
    (date.from_days is a bijection, so this is a sound and complete
    change of representation). A model converter maps models back:
    c := (date.from_days <value of k_c>).

    After this tactic (followed by simplification), goals whose only use
    of Date is through the date operations, Date constants, equality and
    if-then-else contain no Date-sorted terms at all.

Author:

    Claude (Theoria date theory) 2026-07-07

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_elim_dates_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("elim-dates", "eliminate the theory of calendar dates by reduction to integer arithmetic.", "mk_elim_dates_tactic(m, p)")
*/
