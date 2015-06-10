/**
 * \file smt_literal.h
 * \brief SMT-LIB literals.
 */

#ifndef PARSE_SMTLIB_SMT_LITERAL_H
#define PARSE_SMTLIB_SMT_LITERAL_H

#include <string>
#include "smt_abstract.h"
#include "smt_interfaces.h"

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
            T &getValue() {
                return value;
            }

            void setValue(T &value) {
                this->value = value;
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
                               public SpecConstant {
        private:
            unsigned int base;
        public:
            NumeralLiteral(long value, unsigned int base);

            unsigned int getBase();
            void setBase(unsigned int base);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };

        /* ================================== DecimalLiteral ================================== */
        /**
         * Decimal literal.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as a specification constant.
         */
        class DecimalLiteral : public Literal<double>,
                               public SpecConstant {
        public:
            DecimalLiteral(double value);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };

        /* ================================== StringLiteral =================================== */
        /**
         * String literal.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as a specification constant.
         */
        class StringLiteral : public Literal<std::string>,
                              public SpecConstant {
        public:
            StringLiteral(std::string value);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_LITERAL_H