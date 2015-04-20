/**
 * \file smt_basic.h
 * \brief Basic SMT-LIB concepts.
 */

#ifndef PARSE_SMTLIB_SMT_BASIC_H
#define PARSE_SMTLIB_SMT_BASIC_H

#include <string>
#include "smt_abstract.h"
#include "smt_interfaces.h"

namespace smt {
    /* ====================================== Symbol ====================================== */

    /**
     * An SMT-LIB symbol (e.g. "plus", "+", "|quoted symbol|")
     */
    class Symbol : public SmtAstNode {
    private:
        std::string value;
    public:
        /**
         * Constructor
         * \param value     Textual value of the symbol
         */
        Symbol(std::string value);

        std::string getValue();
        void setValue(std::string value);
    };

    /* ====================================== Keyword ===================================== */

    /**
     * An SMT-LIB keyword (e.g. ":date", ":<=")
     */
    class Keyword : public SmtAstNode {
    private:
        std::string value;
    public:
        /**
         * Constructor
         * \param value     Textual value of the keyword
         */
        Keyword(std::string value);

        std::string getValue();
        void setValue(std::string value);
    };

    /* ================================= MetaSpecConstant ================================= */
    /**
     * An SMT-LIB meta specification constant ("NUMERAL", "DECIMAL" or "STRING")
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
         * Constructor
         * \param type  Meta specification constant type
         */
        MetaSpecConstant(MetaSpecConstant::Type type);

        MetaSpecConstant::Type getType();
        void setType(MetaSpecConstant::Type type);
    private:
        MetaSpecConstant::Type type;
    };

    /* =================================== BooleanValue =================================== */
    /**
     * A boolean value ("true" or "false")
     */
    class BooleanValue : public AstNode {
    public:
        /**
         * Types of boolean values
         */
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