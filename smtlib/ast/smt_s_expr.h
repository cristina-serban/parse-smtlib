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
        class CompSExpression : public SExpression,
                                public AttributeValue {
        private:
            std::vector<std::shared_ptr<SExpression>> exprs;
        public:
            /**
             * \param exprs     Subexpressions
             */
            CompSExpression(const std::vector<std::shared_ptr<SExpression>> &exprs);

            std::vector<std::shared_ptr<SExpression>> &getExpressions();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_S_EXPR_H