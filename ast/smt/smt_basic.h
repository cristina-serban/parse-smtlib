#ifndef PARSE_SMTLIB_SMT_BASIC_H
#define PARSE_SMTLIB_SMT_BASIC_H

#include <string>
#include "smt_abstract.h"
#include "smt_interfaces.h"

namespace smt {
    class Symbol : public SmtAstNode {
    private:
        std::string value;
    public:
        Symbol(std::string value);

        std::string getValue();
        void setValue(std::string value);
    };

    class Keyword : public SmtAstNode {
    private:
        std::string value;
    public:
        Keyword(std::string value);

        std::string getValue();
        void setValue(std::string value);
    };

    class MetaSpecConstant : public AstNode {
    public:
        enum Type {
            META_SPEC_NUMERAL = 0,
            META_SPEC_DECIMAL,
            META_SPEC_STRING
        };

        MetaSpecConstant(MetaSpecConstant::Type type);

        MetaSpecConstant::Type getType();
        void setType(MetaSpecConstant::Type type);
    private:
        MetaSpecConstant::Type type;
    };

    class BooleanValue : public AstNode {
    public:
        enum Type {
            BOOL_TRUE = 0,
            BOOL_FALSE
        };

        BooleanValue(BooleanValue::Type type);

        BooleanValue::Type getType();
        void setType(BooleanValue::Type type);
    private:
        BooleanValue::Type type;
    };
}

#endif //PARSE_SMTLIB_SMT_BASIC_H