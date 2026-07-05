/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_factory.h

Abstract:

    Value factory for the Date sort. Values are canonical
    (date.mk y m d) terms, generated from epoch day numbers.

Author:

    Z3 date theory extension 2026-07-05

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "model/value_factory.h"

class date_factory : public simple_factory<rational> {
    date_util m_util;

    app* mk_value_core(rational const& val, sort* s) override {
        return m_util.mk_date_value(val);
    }

public:
    date_factory(ast_manager& m, family_id fid):
        simple_factory<rational>(m, fid),
        m_util(m) {}
};
