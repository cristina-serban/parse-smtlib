#include "ast_script.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

Script::Script(vector<shared_ptr<Command>>& commands) {
    this->commands.insert(this->commands.end(), commands.begin(), commands.end());
}

void Script::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string Script::toString() {
    stringstream ss;
    for(vector<shared_ptr<Command>>::iterator it = commands.begin(); it != commands.end(); it++) {
        ss << (*it)->toString() << "\n";
    }
    return ss.str();
}