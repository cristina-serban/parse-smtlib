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
    for (auto commandIt = commands.begin(); commandIt != commands.end(); commandIt++) {
        ss << (*commandIt)->toString() << "\n";
    }
    return ss.str();
}