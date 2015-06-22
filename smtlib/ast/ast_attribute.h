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

#include <memory>
#include <string>
#include <vector>

namespace smtlib {
    namespace ast {
        /* ==================================== Attribute ===================================== */
        /**
         * An SMT-LIB attribute
         */
        class Attribute : public AstNode {
        private:
            std::shared_ptr<Keyword> keyword;
            std::shared_ptr<AttributeValue> value;

        public:
            /**
             * Default constructor.
             */
            Attribute() { }

            /**
             * Constructs keyword without attribute value.
             * \param keyword   Keyword of the attribute
             */
            Attribute(std::shared_ptr<Keyword> keyword) : keyword(keyword) { }

            /**
             * Constructs keyword with attribute value.
             * \param keyword   Keyword of the attribute
             * \param value     Value of the attribute
             */
            Attribute(std::shared_ptr<Keyword> keyword,
                      std::shared_ptr<AttributeValue> value)
                    : keyword(keyword), value(value) { }

            const std::shared_ptr<Keyword> getKeyword() const;
            std::shared_ptr<Keyword> getKeyword();

            void setKeyword(std::shared_ptr<Keyword> keyword);

            const std::shared_ptr<AttributeValue> getValue() const;
            std::shared_ptr<AttributeValue> getValue();

            void setValue(std::shared_ptr<AttributeValue> value);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ============================== CompoundAttributeValue ============================== */
        /**
         * A compound value for an SMT-LIB attribute
         */
        class CompoundAttributeValue : public AttributeValue {
        private:
            std::vector<std::shared_ptr<AttributeValue>> values;
        public:
            CompoundAttributeValue(const std::vector<std::shared_ptr<AttributeValue>> values);

            const std::vector<std::shared_ptr<AttributeValue>> &getValues() const;
            std::vector<std::shared_ptr<AttributeValue>> &getValues();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };
    }
}

#endif //PARSE_SMTLIB_AST_ATTR_H