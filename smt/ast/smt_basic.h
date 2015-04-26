/**
 * \file smt_basic.h
 * \brief Basic SMT-LIB concepts.
 */

#ifndef PARSE_SMTLIB_SMT_BASIC_H
#define PARSE_SMTLIB_SMT_BASIC_H

#include <memory>
#include <string>
#include "smt_abstract.h"
#include "smt_interfaces.h"

namespace smt {
    namespace ast {
        /* ====================================== Symbol ====================================== */
        /**
     * An SMT-LIB symbol (e.g. "plus", "+", "|quoted symbol|").
     * Node of the SMT-LIB abstract syntax tree.
     * Can act as an S-expression, an index.
     */
        class Symbol : public virtual SmtAstNode,
                       public ISExpression,
                       public IIndex {
        private:
            std::string value;
        public:
            /**
             * \param value     Textual value of the symbol
             */
            Symbol(std::string value) : value(value) { }

            std::string getValue();
            void setValue(std::string value);

            virtual std::string toString();
        };

        /* ====================================== Keyword ===================================== */
        /**
     * An SMT-LIB keyword (e.g. ":date", ":<=").
     * Node of the SMT-LIB abstract syntax tree.
     * Can act as an S-expression.
     */
        class Keyword : public virtual SmtAstNode,
                        public ISExpression {
        private:
            std::string value;
        public:
            /**
             * \param value     Textual value of the keyword
             */
            Keyword(std::string value) : value(value) { }

            std::string getValue();
            void setValue(std::string value);

            virtual std::string toString();
        };

        /* ================================= MetaSpecConstant ================================= */
        /**
     * An SMT-LIB meta specification constant ("NUMERAL", "DECIMAL" or "STRING").
     * Node of the SMT-LIB abstract syntax tree.
     */
        class MetaSpecConstant : public SmtAstNode {
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

            MetaSpecConstant::Type getType();
            void setType(MetaSpecConstant::Type type);

            virtual std::string toString();

        private:
            MetaSpecConstant::Type type;
        };

        /* =================================== BooleanValue =================================== */
        /**
     * A boolean value ("true" or "false").
     * Node of the SMT-LIB abstract syntax tree.
     */
        class BooleanValue : public SmtAstNode {
        private:
            bool value;
        public:
            BooleanValue(bool value) : value(value) { }

            bool getValue();
            void setValue(bool value);

            virtual std::string toString();
        };

        /* =================================== PropLiteral ==================================== */
        /**
     * Propositional literal (used for check-sat-assuming).
     * Node of the SMT-LIB abstract syntax tree.
     */
        class PropLiteral : public SmtAstNode {
        private:
            std::shared_ptr<Symbol> symbol;
            bool negated;

        public:
            PropLiteral(std::shared_ptr<Symbol> symbol, bool negated)
                    : symbol(symbol), negated(negated) { }

            std::shared_ptr<Symbol> getSymbol();

            void setSymbol(std::shared_ptr<Symbol> symbol);

            bool isNegated();
            void setNegated(bool negated);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_BASIC_H