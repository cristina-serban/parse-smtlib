/**
 * \file smt_sexp.h
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
                                public AttributeValue, public std::enable_shared_from_this<CompSExpression> {
        private:
            std::vector<std::shared_ptr<SExpression>> exprs;
        public:
            /**
             * \param exprs     Subexpressions
             */
            CompSExpression(std::vector<std::shared_ptr<SExpression>>& exprs);

            inline std::vector<std::shared_ptr<SExpression>>& getExpressions() { return exprs; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_S_EXPR_H