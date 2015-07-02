#ifndef PARSE_SMTLIB_AST_DATATYPE_H
#define PARSE_SMTLIB_AST_DATATYPE_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_literal.h"
#include "ast_sort.h"

namespace smtlib {
    namespace ast {
        /* ================================= SortDeclaration ================================== */
        class SortDeclaration : public AstNode,
                                public std::enable_shared_from_this<SortDeclaration> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<NumeralLiteral> numeral;
        public:
            SortDeclaration(std::shared_ptr<Symbol> symbol,
                            std::shared_ptr<NumeralLiteral> numeral);

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::shared_ptr<NumeralLiteral> getNumeral() { return numeral; }

            inline void setNumeral(std::shared_ptr<NumeralLiteral> numeral) { this->numeral = numeral; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== SelectorDeclaration ================================ */
        class SelectorDeclaration : public AstNode,
                                    public std::enable_shared_from_this<SelectorDeclaration> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<Sort> sort;
        public:
            SelectorDeclaration(std::shared_ptr<Symbol> symbol,
                            std::shared_ptr<Sort> sort);

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::shared_ptr<Sort> getSort() { return sort; }

            inline void setSort(std::shared_ptr<Sort> sort) { this->sort = sort; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== ConstructorDeclaration ============================== */
        class ConstructorDeclaration : public AstNode,
                                       public std::enable_shared_from_this<ConstructorDeclaration> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::vector<std::shared_ptr<SelectorDeclaration>> selectors;
        public:
            ConstructorDeclaration(std::shared_ptr<Symbol> symbol,
                                   std::vector<std::shared_ptr<SelectorDeclaration>>& selectors);

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::vector<std::shared_ptr<SelectorDeclaration>>& getSelectors() { return selectors; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DatatypeDeclaration =============================== */
        class DatatypeDeclaration : public AstNode { };

        /* ============================= SimpleDatatypeDeclaration ============================ */
        class SimpleDatatypeDeclaration : public DatatypeDeclaration,
                                          public std::enable_shared_from_this<SimpleDatatypeDeclaration>  {
        private:
            std::vector<std::shared_ptr<ConstructorDeclaration>> constructors;
        public:
            SimpleDatatypeDeclaration(std::vector<std::shared_ptr<ConstructorDeclaration>>& constructors);

            inline std::vector<std::shared_ptr<ConstructorDeclaration>>& getConstructors() { return constructors; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =========================== ParametricDatatypeDeclaration ========================== */
        class ParametricDatatypeDeclaration : public DatatypeDeclaration,
                                              public std::enable_shared_from_this<ParametricDatatypeDeclaration> {
        private:
            std::vector<std::shared_ptr<Symbol>> params;
            std::vector<std::shared_ptr<ConstructorDeclaration>> constructors;
        public:
            ParametricDatatypeDeclaration(std::vector<std::shared_ptr<Symbol>> params,
                                          std::vector<std::shared_ptr<ConstructorDeclaration>>& constructors);

            inline std::vector<std::shared_ptr<Symbol>>& getParams() { return params; }

            inline std::vector<std::shared_ptr<ConstructorDeclaration>>& getConstructors() { return constructors; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_DATATYPE_H
