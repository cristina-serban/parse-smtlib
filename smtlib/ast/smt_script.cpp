#include <sstream>
#include "smt_script.h"

using namespace std;
using namespace smtlib::ast;

Script::Script(const vector<shared_ptr<Command>> &commands) {
    this->commands.insert(this->commands.end(), commands.begin(), commands.end());
}

std::vector<shared_ptr<Command>> &Script::getCommands() {
    return commands;
}

void Script::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string Script::toString() {
    stringstream ss;
    for(vector<shared_ptr<Command>>::iterator it = commands.begin(); it != commands.end(); it++) {
        ss << (*it)->toString() << "\n";
    }
    return ss.str();
}