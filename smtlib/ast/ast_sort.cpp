#include <sstream>
#include "ast_sort.h"

using namespace std;
using namespace smtlib::ast;

Sort::Sort(shared_ptr<Identifier> identifier,
           const vector<shared_ptr<Sort>> &params)
        : identifier(identifier) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

shared_ptr<Identifier> Sort::getIdentifier() const {
    return identifier;
}

void Sort::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

vector<shared_ptr<Sort>>& Sort::getParams() {
    return params;
}

vector<shared_ptr<Sort>> Sort::getParams() const {
    return params;
}

bool Sort::isParametric() const {
    return !params.empty();
}

void Sort::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string Sort::toString() {
    if(!isParametric()) {
        return identifier->toString();
    } else {
        stringstream ss;
        ss << "( " << identifier->toString() << " ";

        for(vector<shared_ptr<Sort>>::iterator it = params.begin(); it != params.end(); it++) {
            ss << (*it)->toString() << " ";
        }

        ss << ")";
        return ss.str();
    }
}