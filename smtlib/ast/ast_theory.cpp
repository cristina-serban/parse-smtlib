#include "ast_theory.h"

#include <memory>
#include <sstream>

using namespace smtlib::ast;
using namespace std;

Theory::Theory(shared_ptr<Symbol> name,
                     vector<shared_ptr<Attribute>>& attributes)
        : name(name) {
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

void Theory::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string Theory::toString() {
    stringstream ss;
    ss << "(theory  " << name->toString() << " ";

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        if(it != attributes.begin())
            ss << " ";
        ss << (*it)->toString();
    }

    ss << ")";
    return ss.str();
}