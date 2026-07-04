/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    date_factory.h

Abstract:

    Value factory for the Date sort. Values are canonical
    (date.mk y m d) terms over calendar-valid triples; fresh values are
    enumerated through the day-number bijection with the integers.

Author:

    Claude 2026-07-04

--*/
#pragma once

#include "util/rational.h"
#include "ast/date_decl_plugin.h"
#include "model/value_factory.h"

class date_factory final : public value_factory {
    date_util       u;
    rational        m_next;    // day number of the next fresh candidate
    vector<rational> m_used;   // day numbers of registered values
    expr_ref_vector m_trail;

    bool is_used(rational const& rd) const { return m_used.contains(rd); }

    expr* mk_date_of_rata_die(rational const& rd) {
        rational y, mo, d;
        date_util::date_of_rata_die(rd, y, mo, d);
        expr* e = u.mk_date_value(y, mo, d);
        m_trail.push_back(e);
        return e;
    }

public:

    date_factory(ast_manager & m, family_id fid):
        value_factory(m, fid),
        u(m),
        m_next(0),
        m_trail(m) {
    }

    expr* get_some_value(sort* s) override {
        m_used.push_back(rational(0));
        return mk_date_of_rata_die(rational(0)); // 1970-01-01
    }

    bool get_some_values(sort* s, expr_ref& v1, expr_ref& v2) override {
        v1 = mk_date_of_rata_die(rational(0));
        v2 = mk_date_of_rata_die(rational(1));
        m_used.push_back(rational(0));
        m_used.push_back(rational(1));
        return true;
    }

    expr* get_fresh_value(sort* s) override {
        while (is_used(m_next))
            m_next += rational(1);
        m_used.push_back(m_next);
        expr* e = mk_date_of_rata_die(m_next);
        m_next += rational(1);
        return e;
    }

    void register_value(expr* n) override {
        rational y, mo, d;
        if (u.is_value_mk(n, y, mo, d))
            m_used.push_back(date_util::rata_die(y, mo, d));
    }
};
