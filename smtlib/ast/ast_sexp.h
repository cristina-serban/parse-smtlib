/**
 * \file smt_s_expr.h
 * \brief Compound S-expression.
 */

#ifndef PARSE_SMTLIB_AST_S_EXPR_H
#define PARSE_SMTLIB_AST_S_EXPR_H

#include "ast_interfaces.h"

#include <memory>
#include <vector>

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

            const std::vector<std::shared_ptr<SExpression>> &getExpressions() const;
            std::vector<std::shared_ptr<SExpression>> &getExpressions();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };
    }
}

#endif //PARSE_SMTLIB_AST_S_EXPR_H