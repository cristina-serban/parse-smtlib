/**
 * \file smt_logic
 * \brief SMT-LIB logic.
 */

#ifndef PARSE_SMTLIB_SMT_LOGIC_H
#define PARSE_SMTLIB_SMT_LOGIC_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_attribute.h"

namespace smt {
    namespace ast {
        /**
         * SMT-LIB logic.
         * Node and (possible) root of the SMT abstract syntax tree.
         * Represents the contents of a logic file.
         */
        class SmtLogic : public SmtObject {
        private:
            std::shared_ptr<Symbol> name;
            std::vector<std::shared_ptr<Attribute>> attributes;

        public:
            /**
             * Constructs logic without attributes.
             * \param name          Logic name
             */
            SmtLogic(std::shared_ptr<Symbol> name) : name(name) { }

            /**
             * Constructs logic with attributes.
             * \param name          Logic name
             * \param attributes    Logic attributes
             */
            SmtLogic(std::shared_ptr<Symbol> name,
                     const std::vector<std::shared_ptr<Attribute>> &attributes);

            std::shared_ptr<Symbol> getName();
            void setName(std::shared_ptr<Symbol> name);

            std::vector<std::shared_ptr<Attribute>> &getAttributes();

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_LOGIC_H