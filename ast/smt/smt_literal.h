//
// Created by cristinaserban on 17.04.2015.
//

#ifndef PARSE_SMTLIB_SMT_LITERAL_H
#define PARSE_SMTLIB_SMT_LITERAL_H

#include <string>
#include "smt_abstract.h"
#include "smt_interfaces.h"

namespace smt {
    template <class T>
    class Literal : public virtual SmtAstNode {
    protected:
        T value;

        Literal() { }
    public:
        T& getValue();
        void setValue(T& value);
    };

    class NumeralLiteral : public Literal<long>,
                           public IIndex,
                           public ISpecConstant {
    public:
        NumeralLiteral(long value);
    };

    class DecimalLiteral : public Literal<double>,
                           public ISpecConstant {
    public:
        DecimalLiteral(double value);
    };

    class StringLiteral : public Literal<std::string>,
                          public ISpecConstant {
    public:
        StringLiteral(std::string value);
    };
}


#endif //PARSE_SMTLIB_SMT_LITERAL_H
