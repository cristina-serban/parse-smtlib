/**
 * \file smt_attribute.h
 * \brief Definition of an SMT-LIB attribute.
 */


#ifndef PARSE_SMTLIB_SMT_ATTR_H
#define PARSE_SMTLIB_SMT_ATTR_H

#include <memory>
#include <string>
#include "smt_abstract.h"
#include "smt_basic.h"
#include "smt_interfaces.h"

namespace smt {
    /**
     * An SMT-LIB attribute
     */
    class Attribute : public SmtAstNode {
    private:
        std::shared_ptr<Keyword> keyword;
        std::shared_ptr<IAttributeValue> value;

    public:
        /**
         * Default constructor
         */
        Attribute() { }

        /**
         * Constructor
         * \param keyword   Keyword of the attribute
         */
        Attribute(std::shared_ptr<Keyword> keyword);

        /**
         * Constructor
         * \param keyword   Keyword of the attribute
         * \param value     Value of the attribute
         */
        Attribute(std::shared_ptr<Keyword> keyword,
                  std::shared_ptr<IAttributeValue> value);

        std::shared_ptr<Keyword> getKeyword();
        void setKeyword(std::shared_ptr<Keyword> keyword);

        std::shared_ptr<IAttributeValue> getValue();
        void setValue(std::shared_ptr<IAttributeValue> value);
    };
}

#endif //PARSE_SMTLIB_SMT_ATTR_H