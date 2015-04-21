/**
 * \file smt_literal.h
 * \brief SMT-LIB literals.
 */

#ifndef PARSE_SMTLIB_SMT_LITERAL_H
#define PARSE_SMTLIB_SMT_LITERAL_H

#include <string>
#include "smt_abstract.h"
#include "smt_interfaces.h"

namespace smt {

    /* ====================================== Literal ===================================== */

    /**
     * Literal containing a generic value
     * Node of the SMT-LIB abstract syntax tree.
     */
    template <class T>
    class Literal : public virtual SmtAstNode {
    protected:
        T value;

        Literal() { }
    public:
        T& getValue();
        void setValue(T& value);
    };

    /* ================================== NumeralLiteral ================================== */

    /**
     * Numeric literal.
     * Node of the SMT-LIB abstract syntax tree.
     * Can act as an index or a specification constant.
     */
    class NumeralLiteral : public Literal<long>,
                           public IIndex,
                           public ISpecConstant {
    public:
        NumeralLiteral(long value);
    };

    /* ================================== DecimalLiteral ================================== */

    /**
     * Decimal literal.
     * Node of the SMT-LIB abstract syntax tree.
     * Can act as a specification constant.
     */
    class DecimalLiteral : public Literal<double>,
                           public ISpecConstant {
    public:
        DecimalLiteral(double value);
    };

    /* ================================== StringLiteral =================================== */

    /**
     * String literal.
     * Node of the SMT-LIB abstract syntax tree.
     * Can act as a specification constant.
     */
    class StringLiteral : public Literal<std::string>,
                          public ISpecConstant {
    public:
        StringLiteral(std::string value);
    };
}

#endif //PARSE_SMTLIB_SMT_LITERAL_H