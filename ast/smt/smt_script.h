//
// Created by cristinaserban on 16.04.2015.
//

#ifndef PARSE_SMTLIB_SMT_SCRIPT_H
#define PARSE_SMTLIB_SMT_SCRIPT_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_command.h"

namespace smt {
    class SmtScript : public SmtObject {
    private:
        std::vector<std::shared_ptr<Command>> commands;
    public:
        SmtScript();
        SmtScript(std::vector<std::shared_ptr<Command>>& cmds);

        std::vector<std::shared_ptr<Command>>& getCommands();
    };
}


#endif //PARSE_SMTLIB_SMT_SCRIPT_H
