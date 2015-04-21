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
         * Constructor
         * \param value     Textual value of the symbol
         */
        Symbol(std::string value);

        std::string getValue();
        void setValue(std::string value);
    };

    /* ====================================== Keyword ===================================== */

    /**
     * An SMT-LIB keyword (e.g. ":date", ":<=").
     * Node of the SMT-LIB abstract syntax tree.
     * Can act as an S-expression.
     */
    class Keyword : public virtual SmtAstNode,
                    public ISExpression{
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
     * A boolean value ("true" or "false").
     * Node of the SMT-LIB abstract syntax tree.
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
        PropLiteral(std::shared_ptr<Symbol> symbol, bool negated);

        std::shared_ptr<Symbol> getSymbol();
        void setSymbol(std::shared_ptr<Symbol> symbol);

        bool isNegated();
        void setNegated(bool negated);
    };
}

#endif //PARSE_SMTLIB_SMT_BASIC_H