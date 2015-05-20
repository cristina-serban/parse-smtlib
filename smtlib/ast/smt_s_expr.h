/**
 * \file smt_s_expr.h
 * \brief Compound S-expression.
 */

#ifndef PARSE_SMTLIB_SMT_S_EXPR_H
#define PARSE_SMTLIB_SMT_S_EXPR_H

#include <memory>
#include <vector>
#include "smt_interfaces.h"

namespace smtlib {
    namespace ast {
        /**
         * Compound S-expression.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class CompSExpression : public ISExpression,
                                public IAttributeValue {
        private:
            std::vector<std::shared_ptr<ISExpression>> exprs;
        public:
            /**
             * \param exprs     Subexpressions
             */
            CompSExpression(const std::vector<std::shared_ptr<ISExpression>> &exprs);

            std::vector<std::shared_ptr<ISExpression>> &getExpressions();

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_S_EXPR_H