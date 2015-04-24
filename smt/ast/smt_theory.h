/**
 * \file smt_theory.h
 * \brief SMT-LIB theory.
 */

#ifndef PARSE_SMTLIB_SMT_THEORY_H
#define PARSE_SMTLIB_SMT_THEORY_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_attribute.h"

namespace smt {
    namespace ast {

        /**
         * SMT-LIB theory.
         * Node and (possible) root of the SMT abstract syntax tree.
         * Represents the contents of a theory file.
         */
        class SmtTheory : public SmtObject {
        private:
            std::shared_ptr<Symbol> name;
            std::vector<std::shared_ptr<Attribute>> attributes;

        public:
            /**
             * Constructs theory without attributes.
             * \param name  Theory name
             */
            SmtTheory(std::shared_ptr<Symbol> name);

            /**
             * Constructs theory with attributes.
             * \param name          Theory name
             * \param attributes    Theory attributes
             */
            SmtTheory(std::shared_ptr<Symbol> name,
                      const std::vector<std::shared_ptr<Attribute>> &attributes);

            std::shared_ptr<Symbol> getName();
            void setName(std::shared_ptr<Symbol> name);

            std::vector<std::shared_ptr<Attribute>> &getAttributes();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_THEORY_H