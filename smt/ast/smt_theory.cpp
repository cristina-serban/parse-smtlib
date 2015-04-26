#include <memory>
#include <sstream>
#include "smt_theory.h"

using namespace smt::ast;
using namespace std;

SmtTheory::SmtTheory(shared_ptr<Symbol> name,
                     const vector<shared_ptr<Attribute>> &attributes)
        : name(name) {
    this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
}

shared_ptr<Symbol> SmtTheory::getName() {
    return name;
}

void SmtTheory::setName(shared_ptr<Symbol> name) {
    this->name = name;
}

vector<shared_ptr<Attribute>>& SmtTheory::getAttributes() {
    return attributes;
}

string SmtTheory::toString() {
    stringstream ss;
    ss << "( theory  ";

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";
    return ss.str();
}