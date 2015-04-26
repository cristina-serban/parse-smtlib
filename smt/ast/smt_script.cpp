#include <sstream>
#include "smt_script.h"

using namespace std;
using namespace smt::ast;

SmtScript::SmtScript(const vector<shared_ptr<Command>> &commands) {
    this->commands.insert(this->commands.end(), commands.begin(), commands.end());
}

std::vector<shared_ptr<Command>> &SmtScript::getCommands() {
    return commands;
}

string SmtScript::toString() {
    stringstream ss;
    for(vector<shared_ptr<Command>>::iterator it = commands.begin(); it != commands.end(); it++) {
        ss << (*it)->toString() << "\n";
    }
    return ss.str();
}