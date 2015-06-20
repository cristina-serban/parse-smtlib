/**
 * \file smt_var.h
 * \brief SMT-LIB sorted variable and variable binding.
 */

#ifndef PARSE_SMTLIB_AST_VAR_H
#define PARSE_SMTLIB_AST_VAR_H

#include <memory>
#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"
#include "ast_sort.h"

namespace smtlib {
    namespace ast {
        /* ================================== SortedVariable ================================== */
        /**
         * A sorted variable.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SortedVariable : public AstNode {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<Sort> sort;

        public:
            /**
             * \param symbol    Variable name
             * \param sort      Variable sort
             */
            SortedVariable(std::shared_ptr<Symbol> symbol,
                           std::shared_ptr<Sort> sort)
                    : symbol(symbol), sort(sort) { }

            const std::shared_ptr<Symbol> getSymbol() const;
            std::shared_ptr<Symbol> getSymbol();

            void setSymbol(std::shared_ptr<Symbol> symbol);

            const std::shared_ptr<Sort> getSort() const;
            std::shared_ptr<Sort> getSort();

            void setSort(std::shared_ptr<Sort> sort);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ==================================== VarBinding ==================================== */
        /**
         * A variable binding.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class VarBinding : public AstNode {
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

            const std::shared_ptr<Symbol> getSymbol() const;
            std::shared_ptr<Symbol> getSymbol();

            void setSymbol(std::shared_ptr<Symbol> symbol);

            const std::shared_ptr<Term> getTerm() const;
            std::shared_ptr<Term> getTerm();

            void setTerm(std::shared_ptr<Term> term);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };
    }
}

#endif //PARSE_SMTLIB_AST_VAR_H