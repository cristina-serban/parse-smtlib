/**
 * \file smt_basic.h
 * \brief Basic SMT-LIB concepts.
 */

#ifndef PARSE_SMTLIB_AST_BASIC_H
#define PARSE_SMTLIB_AST_BASIC_H

#include <memory>
#include <string>
#include "ast_abstract.h"
#include "ast_interfaces.h"

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
                       public AttributeValue {
        private:
            std::string value;
        public:
            /**
             * \param value     Textual value of the symbol
             */
            Symbol(std::string value) : value(value) { }

            const std::string &getValue() const;
            std::string &getValue();

            void setValue(std::string value);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ====================================== Keyword ===================================== */
        /**
     * An SMT-LIB keyword (e.g. ":date", ":<=").
     * Node of the SMT-LIB abstract syntax tree.
     * Can act as an S-expression.
     */
        class Keyword : public virtual AstNode,
                        public SExpression {
        private:
            std::string value;
        public:
            /**
             * \param value     Textual value of the keyword
             */
            Keyword(std::string value) : value(value) { }

            const std::string &getValue() const;
            std::string &getValue();

            void setValue(std::string value);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================= MetaSpecConstant ================================= */
        /**
     * An SMT-LIB meta specification constant ("NUMERAL", "DECIMAL" or "STRING").
     * Node of the SMT-LIB abstract syntax tree.
     */
        class MetaSpecConstant : public AstNode {
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
            MetaSpecConstant(MetaSpecConstant::Type type) : type(type) { }

            MetaSpecConstant::Type getType() const;

            void setType(MetaSpecConstant::Type type);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;

        private:
            MetaSpecConstant::Type type;
        };

        /* =================================== BooleanValue =================================== */
        /**
     * A boolean value ("true" or "false").
     * Node of the SMT-LIB abstract syntax tree.
     */
        class BooleanValue : public virtual AstNode,
                             public AttributeValue {
        private:
            bool value;
        public:
            BooleanValue(bool value) : value(value) { }

            bool getValue() const;

            void setValue(bool value);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =================================== PropLiteral ==================================== */
        /**
     * Propositional literal (used for check-sat-assuming).
     * Node of the SMT-LIB abstract syntax tree.
     */
        class PropLiteral : public AstNode {
        private:
            std::shared_ptr<Symbol> symbol;
            bool negated;

        public:
            PropLiteral(std::shared_ptr<Symbol> symbol, bool negated)
                    : symbol(symbol), negated(negated) { }

            const std::shared_ptr<Symbol> getSymbol() const;
            std::shared_ptr<Symbol> getSymbol();

            void setSymbol(std::shared_ptr<Symbol> symbol);

            bool isNegated() const;

            void setNegated(bool negated);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };
    }
}

#endif //PARSE_SMTLIB_AST_BASIC_H