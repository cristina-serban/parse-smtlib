//
// Created by cristinaserban on 16.04.2015.
//

#include "smt_script.h"

using namespace std;
using namespace smt;

SmtScript::SmtScript() { }

SmtScript::SmtScript(vector<shared_ptr<Command>>& commands) {
    for(vector<shared_ptr<Command>>::iterator it = commands.begin();
        it != commands.end(); it++) {
        this->commands.push_back(*it);
    }
}

std::vector<shared_ptr<Command>>& SmtScript::getCommands() {
    return commands;
}