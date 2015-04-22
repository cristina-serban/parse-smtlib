/**
 * \file smt_script
 * \brief SMT-LIB script.
 */

#ifndef PARSE_SMTLIB_SMT_SCRIPT_H
#define PARSE_SMTLIB_SMT_SCRIPT_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_command.h"
#include "smt_basic.h"

namespace smt {
    /**
     * SMT-LIB script.
     * Node and (possible) root of the SMT abstract syntax tree.
     * Represents the contents of a query file.
     */
    class SmtScript : public SmtObject {
    private:
        std::vector<std::shared_ptr<Command>> commands;

    public:
        /**
         * Default constructor
         */
        SmtScript() { }

        /**
         * \param cmds    Command list
         */
        SmtScript(std::vector<std::shared_ptr<Command>> &cmds);

        std::vector<std::shared_ptr<Command>> &getCommands();
    };
}

#endif //PARSE_SMTLIB_SMT_SCRIPT_H