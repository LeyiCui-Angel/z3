/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_factory.h

Abstract:

    Value factory for the theory of calendar dates.
    Values are calendar-valid (date.mk y m d) terms with numeral arguments.

Author:

    Claude (Anthropic) 2026-07-04

--*/
#pragma once

#include "ast/date_decl_plugin.h"
#include "model/value_factory.h"

class date_factory final : public value_factory {
    date_util       u;
    rational        m_next_epoch;
    obj_hashtable<expr> m_values;
    expr_ref_vector m_trail;

    app* mk_date_of_epoch(rational const& e) {
        rational y, mo, d;
        date_util::days_to_civil(e, y, mo, d);
        return u.mk_date(y, mo, d);
    }

public:
    date_factory(ast_manager& m, family_id fid):
        value_factory(m, fid),
        u(m),
        m_next_epoch(0),
        m_trail(m) {
    }

    expr* get_some_value(sort* s) override {
        return register_date(mk_date_of_epoch(rational(0)));
    }

    bool get_some_values(sort* s, expr_ref& v1, expr_ref& v2) override {
        v1 = register_date(mk_date_of_epoch(rational(0)));
        v2 = register_date(mk_date_of_epoch(rational(1)));
        return true;
    }

    expr* get_fresh_value(sort* s) override {
        while (true) {
            app* d = mk_date_of_epoch(m_next_epoch);
            m_next_epoch += rational(1);
            if (!m_values.contains(d))
                return register_date(d);
        }
    }

    void register_value(expr* n) override {
        if (!m_values.contains(n)) {
            m_values.insert(n);
            m_trail.push_back(n);
        }
    }

    app* register_date(app* d) {
        register_value(d);
        return d;
    }
};
