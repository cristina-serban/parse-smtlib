//
// Created by cristinaserban on 16.04.2015.
//

#ifndef PARSE_SMTLIB_SMT_LOGIC_H
#define PARSE_SMTLIB_SMT_LOGIC_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_attribute.h"

namespace smt {
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
         * Constructor without attributes
         * \param name          Logic name
         */
        SmtLogic(std::shared_ptr<Symbol> name);

        /**
         * Constructor with attributes
         * \param name          Logic name
         * \param attributes    Logic attributes
         */
        SmtLogic(std::shared_ptr<Symbol> name,
                 std::vector<std::shared_ptr<Attribute>> &attributes);

        std::shared_ptr<Symbol> getName();
        void setName(std::shared_ptr<Symbol> name);

        std::vector<std::shared_ptr<Attribute>> &getAttributes();
    };
}

#endif //PARSE_SMTLIB_SMT_LOGIC_H
