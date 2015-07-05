/**
 * \file ast_attribute.h
 * \brief SMT-LIB attribute.
 */

#ifndef PARSE_SMTLIB_AST_ATTR_H
#define PARSE_SMTLIB_AST_ATTR_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"
#include "../visitor/ast_visitor.h"

#include <vector>

namespace smtlib {
    namespace ast {
        /* ==================================== Attribute ===================================== */
        /**
         * An SMT-LIB attribute
         */
        class Attribute : public AstNode,
                          public std::enable_shared_from_this<Attribute> {
        private:
            std::shared_ptr<Keyword> keyword;
            std::shared_ptr<AttributeValue> value;

        public:
            /**
             * Default constructor.
             */
            inline Attribute() { }

            /**
             * Constructs keyword without attribute value.
             * \param keyword   Keyword of the attribute
             */
            inline Attribute(std::shared_ptr<Keyword> keyword) : keyword(keyword) { }

            /**
             * Constructs keyword with attribute value.
             * \param keyword   Keyword of the attribute
             * \param value     Value of the attribute
             */
            inline Attribute(std::shared_ptr<Keyword> keyword,
                             std::shared_ptr<AttributeValue> value)
                    : keyword(keyword), value(value) { }

            inline std::shared_ptr<Keyword> getKeyword() { return keyword; }

            inline void setKeyword(std::shared_ptr<Keyword> keyword) { this->keyword = keyword; }

            inline std::shared_ptr<AttributeValue> getValue() { return value; }

            inline void setValue(std::shared_ptr<AttributeValue> value) { this->value = value; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ============================== CompAttributeValue ============================== */
        /**
         * A compound value for an SMT-LIB attribute
         */
        class CompAttributeValue : public AttributeValue,
                                   public std::enable_shared_from_this<CompAttributeValue> {
        private:
            std::vector<std::shared_ptr<AttributeValue>> values;
        public:
            /**
             * Constructs a composite attribute value from a vector of attribute values
             * \param values    Vector of attribute values
             */
            CompAttributeValue(std::vector<std::shared_ptr<AttributeValue>>& values);

            inline std::vector<std::shared_ptr<AttributeValue>>& getValues() { return values; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_ATTR_H