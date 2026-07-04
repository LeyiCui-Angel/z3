/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_rewriter.h

Abstract:

    Basic rewriting rules for the Dates theory: concrete evaluation of
    selectors, date arithmetic and comparisons over calendar-valid
    (date.mk y m d) value terms. Applications over invalid constructor
    triples are left untouched, since their meaning is unspecified.

Author:

    Date theory extension 2026-07-04

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"

class date_rewriter {
    ast_manager& m;
    date_util    dt;
    arith_util   a;

    bool is_valid_value(expr* e, rational& y, rational& mo, rational& d) const;

    static rational epoch_of(rational const& y, rational const& mo, rational const& d);
    static void date_of_epoch(rational const& e, rational& y, rational& mo, rational& d);

    br_status mk_add(rational const& y, rational const& mo, rational const& d,
                     rational const& py, rational const& pm, rational const& pd,
                     expr_ref& result);

public:
    date_rewriter(ast_manager& m):
        m(m), dt(m), a(m) {}

    family_id get_fid() const { return dt.get_family_id(); }

    date_util& u() { return dt; }

    br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result);
};
