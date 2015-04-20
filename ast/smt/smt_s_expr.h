/**
 * \file smt_s_expr.h
 * \brief Definition of a compound S-expression.
 */

#ifndef PARSE_SMTLIB_SMT_S_EXPR_H
#define PARSE_SMTLIB_SMT_S_EXPR_H

#include <memory>
#include <vector>
#include "smt_interfaces.h"

namespace smt {
    /**
     * Compound S-expression.
     * Node of the SMT abstract syntax tree.
     */
    class CompSExpression : public ISExpression {
    private:
        std::vector<std::shared_ptr<ISExpression>> exprs;
    public:
        /**
         * Constructor
         * \param exprs     Subexpressions
         */
        CompSExpression(std::vector<std::shared_ptr<ISExpression>> &exprs);

        std::vector<std::shared_ptr<ISExpression>> &getExpressions();
    };
}


#endif //PARSE_SMTLIB_SMT_S_EXPR_H
