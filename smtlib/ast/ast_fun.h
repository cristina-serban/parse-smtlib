/**
 * \file smt_fun.h
 * \brief Function declaration and definition.
 */

#ifndef PARSE_SMTLIB_AST_FUN_H
#define PARSE_SMTLIB_AST_FUN_H

#include <memory>
#include <vector>
#include <visitor/ast_visitor.h>
#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"
#include "ast_sort.h"
#include "ast_var.h"

namespace smtlib {
    namespace ast {
        /* =============================== FunctionDeclaration ================================ */
        /**
         * An SMT-LIB function declaration.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class FunctionDeclaration : public AstNode {
        private:
            std::shared_ptr<Symbol> symbol;
            std::vector<std::shared_ptr<SortedVariable>> params;
            std::shared_ptr<Sort> sort;
        public:
            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param sort      Sort of the return value
             */
            FunctionDeclaration(std::shared_ptr<Symbol> symbol,
                                const std::vector<std::shared_ptr<SortedVariable>> &params,
                                std::shared_ptr<Sort> sort);

            std::shared_ptr<Symbol> getSymbol() const;
            void setSymbol(std::shared_ptr<Symbol> symbol);

            std::vector<std::shared_ptr<SortedVariable>> &getParams();

            std::shared_ptr<Sort> getSort() const;
            void setSort(std::shared_ptr<Sort> sort);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };

        /* ================================ FunctionDefinition ================================ */
        /**
         * An SMT-LIB function definition.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class FunctionDefinition : public AstNode {
        private:
            std::shared_ptr<FunctionDeclaration> signature;
            std::shared_ptr<Term> body;
        public:
            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            FunctionDefinition(std::shared_ptr<FunctionDeclaration> signature,
                               std::shared_ptr<Term> body)
                    : signature(signature), body(body) { }

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            FunctionDefinition(std::shared_ptr<Symbol> symbol,
                               const std::vector<std::shared_ptr<SortedVariable>> &params,
                               std::shared_ptr<Sort> sort,
                               std::shared_ptr<Term> body);

            std::shared_ptr<FunctionDeclaration> getSignature() const;
            void setSignature(std::shared_ptr<FunctionDeclaration> signature);

            std::shared_ptr<Term> getBody() const;
            void setBody(std::shared_ptr<Term> body);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_FUN_H