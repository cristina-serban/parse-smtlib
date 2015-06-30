#include "ast_sort.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

Sort::Sort(shared_ptr<Identifier> identifier,
           vector<shared_ptr<Sort>> &args)
        : identifier(identifier) {
    this->args.insert(this->args.end(), args.begin(), args.end());
}

shared_ptr<Identifier> Sort::getIdentifier() {
    return identifier;
}

void Sort::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

vector<shared_ptr<Sort>> &Sort::getArgs() {
    return args;
}

bool Sort::hasArgs() {
    return !args.empty();
}

void Sort::accept(AstVisitor0* visitor) {
     visitor->visit(shared_from_this());
}

string Sort::toString() {
    if(!hasArgs()) {
        return identifier->toString();
    } else {
        stringstream ss;
        ss << "(" << identifier->toString() << " ";

        for(vector<shared_ptr<Sort>>::iterator it = args.begin(); it != args.end(); it++) {
            if(it != args.begin())
                ss << " ";
            ss << (*it)->toString();
        }

        ss << ")";
        return ss.str();
    }
}