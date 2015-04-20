/**
 * \file smt_theory.h
 * \brief Definition of an SMT-LIB theory
 * */

#ifndef PARSE_SMTLIB_SMT_THEORY_H
#define PARSE_SMTLIB_SMT_THEORY_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_attribute.h"

namespace smt {

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
         * Constructor without attributes
         * \param name  Theory name
         */
        SmtTheory(std::shared_ptr<Symbol> name);

        /**
         * Constructor with attributes
         * \param name          Theory name
         * \param attributes    Theory attributes
         */
        SmtTheory(std::shared_ptr<Symbol> name,
                  std::vector<std::shared_ptr<Attribute>>& attributes);

        std::shared_ptr<Symbol> getName();
        void setName(std::shared_ptr<Symbol> name);

        std::vector<std::shared_ptr<Attribute>>& getAttributes();
    };
}


#endif //PARSE_SMTLIB_SMT_THEORY_H
