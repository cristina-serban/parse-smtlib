/**
 * \file smt_basic.h
 * \brief Basic SMT-LIB concepts.
 */

#ifndef PARSE_SMTLIB_AST_BASIC_H
#define PARSE_SMTLIB_AST_BASIC_H

#include "ast_abstract.h"
#include "ast_interfaces.h"

#include <memory>
#include <string>

namespace smtlib {
    namespace ast {
        /* ====================================== Symbol ====================================== */
        /**
     * An SMT-LIB symbol (e.g. "plus", "+", "|quoted symbol|").
     * Node of the SMT-LIB abstract syntax tree.
     * Can act as an S-expression, an index.
     */
        class Symbol : public virtual AstNode,
                       public SExpression,
                       public Index,
                       public AttributeValue,
                       public Constructor,
                       public std::enable_shared_from_this<Symbol> {
        private:
            std::string value;
        public:
            /**
             * \param value     Textual value of the symbol
             */
            inline Symbol(std::string value) : value(value) { }

            inline std::string &getValue() { return value; }

            inline void setValue(std::string value) { this->value = value; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ====================================== Keyword ===================================== */
        /**
     * An SMT-LIB keyword (e.g. ":date", ":<=").
     * Node of the SMT-LIB abstract syntax tree.
     * Can act as an S-expression.
     */
        class Keyword : public virtual AstNode,
                        public SExpression,
                        public std::enable_shared_from_this<Keyword> {
        private:
            std::string value;
        public:
            /**
             * \param value     Textual value of the keyword
             */
            inline Keyword(std::string value) : value(value) { }

            inline std::string &getValue() { return value; }

            inline void setValue(std::string value) { this->value = value; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= MetaSpecConstant ================================= */
        /**
     * An SMT-LIB meta specification constant ("NUMERAL", "DECIMAL" or "STRING").
     * Node of the SMT-LIB abstract syntax tree.
     */
        class MetaSpecConstant : public AstNode,
                                 public std::enable_shared_from_this<MetaSpecConstant> {
        public:
            /**
             * Types of meta specification constants
             */
            enum Type {
                META_SPEC_NUMERAL = 0,
                META_SPEC_DECIMAL,
                META_SPEC_STRING
            };

            /**
             * \param type  Meta specification constant type
             */
            inline MetaSpecConstant(MetaSpecConstant::Type type) : type(type) { }

            inline MetaSpecConstant::Type getType() { return type; }

            inline void setType(MetaSpecConstant::Type type) { this->type = type; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        private:
            MetaSpecConstant::Type type;
        };

        /* =================================== BooleanValue =================================== */
        /**
     * A boolean value ("true" or "false").
     * Node of the SMT-LIB abstract syntax tree.
     */
        class BooleanValue : public virtual AstNode,
                             public AttributeValue,
                             public std::enable_shared_from_this<BooleanValue> {
        private:
            bool value;
        public:
            inline BooleanValue(bool value) : value(value) { }

            inline bool getValue() { return value; }

            inline void setValue(bool value) { this->value = value; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== PropLiteral ==================================== */
        /**
     * Propositional literal (used for check-sat-assuming).
     * Node of the SMT-LIB abstract syntax tree.
     */
        class PropLiteral : public AstNode,
                            public std::enable_shared_from_this<PropLiteral> {
        private:
            std::shared_ptr<Symbol> symbol;
            bool negated;

        public:
            inline PropLiteral(std::shared_ptr<Symbol> symbol, bool negated)
                    : symbol(symbol), negated(negated) { }

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline bool isNegated() { return negated; }

            inline void setNegated(bool negated) { this->negated = negated; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_BASIC_H