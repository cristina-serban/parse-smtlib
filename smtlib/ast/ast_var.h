/**
 * \file smt_var.h
 * \brief SMT-LIB sorted variable and variable binding.
 */

#ifndef PARSE_SMTLIB_AST_VAR_H
#define PARSE_SMTLIB_AST_VAR_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"
#include "ast_sort.h"

#include <memory>

namespace smtlib {
    namespace ast {
        /* ================================== SortedVariable ================================== */
        /**
         * A sorted variable.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SortedVariable : public AstNode, public std::enable_shared_from_this<SortedVariable> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<Sort> sort;

        public:
            /**
             * \param symbol    Variable name
             * \param sort      Variable sort
             */
            inline SortedVariable(std::shared_ptr<Symbol> symbol,
                                  std::shared_ptr<Sort> sort)
                    : symbol(symbol), sort(sort) { }

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::shared_ptr<Sort> getSort() { return sort; }

            inline void setSort(std::shared_ptr<Sort> sort) { this->sort = sort; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== VarBinding ==================================== */
        /**
         * A variable binding.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class VarBinding : public AstNode, public std::enable_shared_from_this<VarBinding> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<Term> term;

        public:
            /**
             * \param symbol    Variable name
             * \param term      Binding
             */
            VarBinding(std::shared_ptr<Symbol> symbol,
                       std::shared_ptr<Term> term)
                    : symbol(symbol), term(term) {
            }

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::shared_ptr<Term> getTerm() { return term; }

            inline void setTerm(std::shared_ptr<Term> term) { this->term = term; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_VAR_H