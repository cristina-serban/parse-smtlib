/**
 * \file smt_fun.h
 * \brief Function declaration and definition.
 */

#ifndef PARSE_SMTLIB_SMT_FUN_H
#define PARSE_SMTLIB_SMT_FUN_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_basic.h"
#include "smt_interfaces.h"
#include "smt_sort.h"
#include "smt_var.h"

namespace smt {
    namespace ast {
        /* =============================== FunctionDeclaration ================================ */
        /**
         * An SMT-LIB function declaration.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class FunctionDeclaration : public SmtAstNode {
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

            std::shared_ptr<Symbol> getSymbol();
            void setSymbol(std::shared_ptr<Symbol> symbol);

            std::vector<std::shared_ptr<SortedVariable>> &getParams();

            std::shared_ptr<Sort> getSort();
            void setSort(std::shared_ptr<Sort> sort);

            virtual std::string toString();
        };

        /* ================================ FunctionDefinition ================================ */
        /**
         * An SMT-LIB function definition.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class FunctionDefinition : public SmtAstNode {
        private:
            std::shared_ptr<FunctionDeclaration> signature;
            std::shared_ptr<ITerm> body;
        public:
            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            FunctionDefinition(std::shared_ptr<FunctionDeclaration> signature,
                               std::shared_ptr<ITerm> body);

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            FunctionDefinition(std::shared_ptr<Symbol> symbol,
                               const std::vector<std::shared_ptr<SortedVariable>> &params,
                               std::shared_ptr<Sort> sort,
                               std::shared_ptr<ITerm> body);

            std::shared_ptr<FunctionDeclaration> getSignature();
            void setSignature(std::shared_ptr<FunctionDeclaration> signature);

            std::shared_ptr<ITerm> getBody();
            void setBody(std::shared_ptr<ITerm> body);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_FUN_H