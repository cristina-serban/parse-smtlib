#include "ast_sort.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

Sort::Sort(shared_ptr<Identifier> identifier,
           const vector<shared_ptr<Sort>> &params)
        : identifier(identifier) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

const shared_ptr<Identifier> Sort::getIdentifier() const {
    return identifier;
}

shared_ptr<Identifier> Sort::getIdentifier() {
    return identifier;
}

void Sort::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

const vector<shared_ptr<Sort>>& Sort::getParams() const {
    return params;
}

vector<shared_ptr<Sort>> &Sort::getParams() {
    return params;
}

bool Sort::isParametrized() const {
    return !params.empty();
}

void Sort::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string Sort::toString() const {
    if(!isParametrized()) {
        return identifier->toString();
    } else {
        stringstream ss;
        ss << "(" << identifier->toString() << " ";

        for(vector<shared_ptr<Sort>>::const_iterator it = params.begin(); it != params.end(); it++) {
            if(it != params.begin())
                ss << " ";
            ss << (*it)->toString();
        }

        ss << ")";
        return ss.str();
    }
}