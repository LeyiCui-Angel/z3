/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_factory.h

Abstract:

    Value factory for the theory of calendar dates. Values are canonical
    (date.mk y m d) terms over calendar-valid numeral triples. Fresh
    values enumerate successive days starting from the epoch through the
    rata-die bijection.

Author:

    Date theory extension 2026-07-05

--*/
#pragma once

#include "model/value_factory.h"
#include "ast/date_decl_plugin.h"

class date_factory final : public value_factory {
    date_util          u;
    obj_hashtable<expr> m_values;
    rational           m_next_day { 0 };
    expr_ref_vector    m_trail;

    app* mk_day_number(rational const& n) {
        rational y, mo, d;
        date_util::civil_from_days(n, y, mo, d);
        app* val = u.mk_date_value(y, mo, d);
        m_trail.push_back(val);
        return val;
    }

public:
    date_factory(ast_manager& m, family_id fid):
        value_factory(m, fid),
        u(m),
        m_trail(m) {
    }

    expr* get_some_value(sort* s) override {
        return mk_day_number(rational(0));
    }

    bool get_some_values(sort* s, expr_ref& v1, expr_ref& v2) override {
        v1 = mk_day_number(rational(0));
        v2 = mk_day_number(rational(1));
        return true;
    }

    expr* get_fresh_value(sort* s) override {
        app* val = mk_day_number(m_next_day);
        while (m_values.contains(val)) {
            m_next_day += rational(1);
            val = mk_day_number(m_next_day);
        }
        m_values.insert(val);
        return val;
    }

    void register_value(expr* n) override {
        rational y, mo, d;
        if (u.is_date_value(n, y, mo, d) && !m_values.contains(n)) {
            m_trail.push_back(n);
            m_values.insert(n);
        }
    }

    void add_trail(expr* e) {
        m_trail.push_back(e);
    }
};
