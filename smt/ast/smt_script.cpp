#include "smt_script.h"

using namespace std;
using namespace smt::ast;

SmtScript::SmtScript(const vector<shared_ptr<Command>> &commands) {
    this->commands.insert(this->commands.end(), commands.begin(), commands.end());
}

std::vector<shared_ptr<Command>> &SmtScript::getCommands() {
    return commands;
}