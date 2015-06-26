#include "ast_sort.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

Sort::Sort(shared_ptr<Identifier> identifier,
           vector<shared_ptr<Sort>> &params)
        : identifier(identifier) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

shared_ptr<Identifier> Sort::getIdentifier() {
    return identifier;
}

void Sort::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

vector<shared_ptr<Sort>> &Sort::getParams() {
    return params;
}

bool Sort::isParametrized() {
    return !params.empty();
}

void Sort::accept(AstVisitor0* visitor) {
     visitor->visit(shared_from_this());
}

string Sort::toString() {
    if(!isParametrized()) {
        return identifier->toString();
    } else {
        stringstream ss;
        ss << "(" << identifier->toString() << " ";

        for(vector<shared_ptr<Sort>>::iterator it = params.begin(); it != params.end(); it++) {
            if(it != params.begin())
                ss << " ";
            ss << (*it)->toString();
        }

        ss << ")";
        return ss.str();
    }
}