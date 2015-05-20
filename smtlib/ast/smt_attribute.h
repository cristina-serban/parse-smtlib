/**
 * \file smt_attribute.h
 * \brief SMT-LIB attribute.
 */

#ifndef PARSE_SMTLIB_SMT_ATTR_H
#define PARSE_SMTLIB_SMT_ATTR_H

#include <memory>
#include <string>
#include <vector>
#include "smt_abstract.h"
#include "smt_basic.h"
#include "smt_interfaces.h"

namespace smtlib {
    namespace ast {
        /* ==================================== Attribute ===================================== */
        /**
         * An SMT-LIB attribute
         */
        class Attribute : public AstNode {
        private:
            std::shared_ptr<Keyword> keyword;
            std::shared_ptr<IAttributeValue> value;

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
                      std::shared_ptr<IAttributeValue> value)
                    : keyword(keyword), value(value) { }

            std::shared_ptr<Keyword> getKeyword();
            void setKeyword(std::shared_ptr<Keyword> keyword);

            std::shared_ptr<IAttributeValue> getValue();
            void setValue(std::shared_ptr<IAttributeValue> value);

            virtual std::string toString();
        };

        /* ============================== CompoundAttributeValue ============================== */
        /**
         * A compound value for an SMT-LIB attribute
         */
        class CompoundAttributeValue : public IAttributeValue {
        private:
            std::vector<std::shared_ptr<IAttributeValue>> values;
        public:
            CompoundAttributeValue(const std::vector<std::shared_ptr<IAttributeValue>> values);

            std::vector<std::shared_ptr<IAttributeValue>> &getValues();

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_ATTR_H