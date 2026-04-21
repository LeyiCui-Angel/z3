/*++
Copyright (c) 2026 CMU PASTA Lab

Module Name:

    date_decl_plugin.h

Abstract:

    Declaration plugin for the Date theory.

    Introduces one sort (Date) and the following function symbols:
      date.mk    (Int Int Int -> Date)          constructor
      date.year  (Date -> Int)                  year selector
      date.month (Date -> Int)                  month selector
      date.day   (Date -> Int)                  day selector
      date.add   (Date Int Int Int -> Date)     add period
      date.sub   (Date Int Int Int -> Date)     subtract period
      date.lt    (Date Date -> Bool)            strict less-than
      date.le    (Date Date -> Bool)            less-than-or-equal
      date.gt    (Date Date -> Bool)            strict greater-than
      date.ge    (Date Date -> Bool)            greater-than-or-equal

Author:

    Angel Cui

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"

enum date_sort_kind {
    DATE_SORT,
    LAST_DATE_SORT
};

enum date_op_kind {
    OP_DATE_MK,      // Int Int Int -> Date
    OP_DATE_YEAR,    // Date -> Int
    OP_DATE_MONTH,   // Date -> Int
    OP_DATE_DAY,     // Date -> Int
    OP_DATE_ADD,     // Date Int Int Int -> Date
    OP_DATE_SUB,     // Date Int Int Int -> Date
    OP_DATE_LT,      // Date Date -> Bool
    OP_DATE_LE,      // Date Date -> Bool
    OP_DATE_GT,      // Date Date -> Bool
    OP_DATE_GE,      // Date Date -> Bool
    LAST_DATE_OP
};

class date_decl_plugin : public decl_plugin {
    sort* m_date_sort { nullptr };

public:
    date_decl_plugin() = default;
    ~date_decl_plugin() override;

    void finalize() override;
    void set_manager(ast_manager* m, family_id id) override;

    decl_plugin* mk_fresh() override { return alloc(date_decl_plugin); }

    sort* mk_sort(decl_kind k, unsigned num_params, parameter const* params) override;

    func_decl* mk_func_decl(decl_kind k, unsigned num_params, parameter const* params,
                             unsigned arity, sort* const* domain, sort* range) override;

    void get_op_names(svector<builtin_name>& op_names, symbol const& logic) override;
    void get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) override;

    expr* get_some_value(sort* s) override;
};

// Utility class for building and recognizing date expressions
class date_util {
    ast_manager& m;
    mutable family_id m_fid { null_family_id };
    arith_util m_autil;

    family_id fid() const;

public:
    date_util(ast_manager& m) : m(m), m_autil(m) {}

    family_id get_family_id() const { return fid(); }

    sort* get_date_sort() const;

    bool is_date(sort const* s) const;
    bool is_date(expr const* e) const;

    bool is_date_mk   (expr const* e) const { return is_app_of(e, fid(), OP_DATE_MK);    }
    bool is_date_year (expr const* e) const { return is_app_of(e, fid(), OP_DATE_YEAR);  }
    bool is_date_month(expr const* e) const { return is_app_of(e, fid(), OP_DATE_MONTH); }
    bool is_date_day  (expr const* e) const { return is_app_of(e, fid(), OP_DATE_DAY);   }
    bool is_date_add  (expr const* e) const { return is_app_of(e, fid(), OP_DATE_ADD);   }
    bool is_date_sub  (expr const* e) const { return is_app_of(e, fid(), OP_DATE_SUB);   }
    bool is_date_lt   (expr const* e) const { return is_app_of(e, fid(), OP_DATE_LT);    }
    bool is_date_le   (expr const* e) const { return is_app_of(e, fid(), OP_DATE_LE);    }
    bool is_date_gt   (expr const* e) const { return is_app_of(e, fid(), OP_DATE_GT);    }
    bool is_date_ge   (expr const* e) const { return is_app_of(e, fid(), OP_DATE_GE);    }

    bool is_date_cmp(expr const* e) const {
        return is_date_lt(e) || is_date_le(e) || is_date_gt(e) || is_date_ge(e);
    }

    app* mk_date (expr* y, expr* mo, expr* d);
    app* mk_year (expr* d);
    app* mk_month(expr* d);
    app* mk_day  (expr* d);
    app* mk_add  (expr* d, expr* py, expr* pm, expr* pd);
    app* mk_sub  (expr* d, expr* py, expr* pm, expr* pd);
    app* mk_lt   (expr* d1, expr* d2);
    app* mk_le   (expr* d1, expr* d2);
    app* mk_gt   (expr* d1, expr* d2);
    app* mk_ge   (expr* d1, expr* d2);

    arith_util& arith() { return m_autil; }
    ast_manager& get_manager() { return m; }
};
