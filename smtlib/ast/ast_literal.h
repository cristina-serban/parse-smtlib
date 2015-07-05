/**
 * \file smt_literal.h
 * \brief SMT-LIB literals.
 */

#ifndef PARSE_SMTLIB_AST_LITERAL_H
#define PARSE_SMTLIB_AST_LITERAL_H

#include "ast_abstract.h"
#include "ast_interfaces.h"

#include <string>

namespace smtlib {
    namespace ast {
        /* ====================================== Literal ===================================== */
        /**
         * Literal containing a generic value
         * Node of the SMT-LIB abstract syntax tree.
         */
        template<class T>
        class Literal : public virtual AstNode {
        protected:
            T value;

            Literal() { }

        public:
            inline T &getValue() { return value; }

            inline void setValue(T &value) { this->value = value;
            }
        };

        /* ================================== NumeralLiteral ================================== */
        /**
         * Numeric literal.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as an index or a specification constant.
         */
        class NumeralLiteral : public Literal<long>,
                               public Index,
                               public SpecConstant, public std::enable_shared_from_this<NumeralLiteral> {
        private:
            unsigned int base;
        public:
            inline NumeralLiteral(long value, unsigned int base)
                    : base(base) { this->value = value; }

            inline unsigned int getBase() { return base; }

            inline void setBase(unsigned int base) { this->base = base; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================== DecimalLiteral ================================== */
        /**
         * Decimal literal.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as a specification constant.
         */
        class DecimalLiteral : public Literal<double>,
                               public SpecConstant, public std::enable_shared_from_this<DecimalLiteral> {
        public:
            inline DecimalLiteral(double value) { this->value = value; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================== StringLiteral =================================== */
        /**
         * String literal.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as a specification constant.
         */
        class StringLiteral : public Literal<std::string>,
                              public SpecConstant,
                              public std::enable_shared_from_this<StringLiteral> {
        public:
            inline StringLiteral(std::string value) { this->value = value; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_LITERAL_H