/**
 * \file smt_datatype.h
 * \brief SMT-LIB datatype declarations and their components.
 */

#ifndef PARSE_SMTLIB_AST_DATATYPE_H
#define PARSE_SMTLIB_AST_DATATYPE_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_literal.h"
#include "ast_sort.h"

namespace smtlib {
    namespace ast {
        /* ================================= SortDeclaration ================================== */
        /**
         * A sort declaration (used by the declare-datatypes command).
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SortDeclaration : public AstNode,
                                public std::enable_shared_from_this<SortDeclaration> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<NumeralLiteral> numeral;
        public:
            /**
             * \param symbol    Datatype (sort) name
             * \param numeral   Arity
             */
            inline SortDeclaration(std::shared_ptr<Symbol> symbol,
                                   std::shared_ptr<NumeralLiteral> numeral)
                    : symbol(symbol), numeral(numeral) { }

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::shared_ptr<NumeralLiteral> getNumeral() { return numeral; }

            inline void setNumeral(std::shared_ptr<NumeralLiteral> numeral) { this->numeral = numeral; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== SelectorDeclaration ================================ */
        /**
         * A selector declaration (used by constructor declarations).
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SelectorDeclaration : public AstNode,
                                    public std::enable_shared_from_this<SelectorDeclaration> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<Sort> sort;
        public:
            /**
             * \param symbol    Selector name
             * \param sort      Selector sort
             */
            inline SelectorDeclaration(std::shared_ptr<Symbol> symbol,
                                       std::shared_ptr<Sort> sort)
                    : symbol(symbol), sort(sort) { }

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::shared_ptr<Sort> getSort() { return sort; }

            inline void setSort(std::shared_ptr<Sort> sort) { this->sort = sort; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== ConstructorDeclaration ============================== */
        /**
         * A sort declaration (used by the declare-datatypes command).
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ConstructorDeclaration : public AstNode,
                                       public std::enable_shared_from_this<ConstructorDeclaration> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::vector<std::shared_ptr<SelectorDeclaration>> selectors;
        public:
            /**
             * \param symbol        Constructor name
             * \param selectors     Selectors for the constructor
             */
            ConstructorDeclaration(std::shared_ptr<Symbol> symbol,
                                   std::vector<std::shared_ptr<SelectorDeclaration>>& selectors);

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::vector<std::shared_ptr<SelectorDeclaration>>& getSelectors() { return selectors; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DatatypeDeclaration =============================== */
        /**
         * A datatype declaration (used by the declare-datatype and declare-datatypes commands).
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DatatypeDeclaration : public AstNode { };

        /* ============================= SimpleDatatypeDeclaration ============================ */
        /**
         * A simple (non-parametric) datatype declaration.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SimpleDatatypeDeclaration : public DatatypeDeclaration,
                                          public std::enable_shared_from_this<SimpleDatatypeDeclaration>  {
        private:
            std::vector<std::shared_ptr<ConstructorDeclaration>> constructors;
        public:
            /**
             * \param constructors  Constructors for this datatype
             */
            SimpleDatatypeDeclaration(std::vector<std::shared_ptr<ConstructorDeclaration>>& constructors);

            inline std::vector<std::shared_ptr<ConstructorDeclaration>>& getConstructors() { return constructors; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =========================== ParametricDatatypeDeclaration ========================== */
        /**
         * A parametric datatype declaration.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ParametricDatatypeDeclaration : public DatatypeDeclaration,
                                              public std::enable_shared_from_this<ParametricDatatypeDeclaration> {
        private:
            std::vector<std::shared_ptr<Symbol>> params;
            std::vector<std::shared_ptr<ConstructorDeclaration>> constructors;
        public:
            /**
             * \param params        Parameters for the declaration
             * \param constructors  Constructors for this datatype
             */
            ParametricDatatypeDeclaration(std::vector<std::shared_ptr<Symbol>>& params,
                                          std::vector<std::shared_ptr<ConstructorDeclaration>>& constructors);

            inline std::vector<std::shared_ptr<Symbol>>& getParams() { return params; }

            inline std::vector<std::shared_ptr<ConstructorDeclaration>>& getConstructors() { return constructors; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_DATATYPE_H
