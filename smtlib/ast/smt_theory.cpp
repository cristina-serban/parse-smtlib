#include <memory>
#include <sstream>
#include "smt_theory.h"

using namespace smtlib::ast;
using namespace std;

Theory::Theory(shared_ptr<Symbol> name,
                     const vector<shared_ptr<Attribute>> &attributes)
        : name(name) {
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

shared_ptr<Symbol> Theory::getName() {
    return name;
}

void Theory::setName(shared_ptr<Symbol> name) {
    this->name = name;
}

vector<shared_ptr<Attribute>>&Theory::getAttributes() {
    return attributes;
}

void Theory::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string Theory::toString() {
    stringstream ss;
    ss << "( theory  " << name->toString() << " ";

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";
    return ss.str();
}