#include <sstream>
#include "smt_script.h"

using namespace std;
using namespace smt::ast;

Script::Script(const vector<shared_ptr<Command>> &commands) {
    this->commands.insert(this->commands.end(), commands.begin(), commands.end());
}

std::vector<shared_ptr<Command>> &Script::getCommands() {
    return commands;
}

string Script::toString() {
    stringstream ss;
    for(vector<shared_ptr<Command>>::iterator it = commands.begin(); it != commands.end(); it++) {
        ss << (*it)->toString() << "\n";
    }
    return ss.str();
}