#include <memory>
#include "smt_theory.h"

using namespace smt::ast;
using namespace std;

SmtTheory::SmtTheory(shared_ptr<Symbol> name) {
    setName(name);
}

SmtTheory::SmtTheory(shared_ptr<Symbol> name, vector<shared_ptr<Attribute>> &attributes) {
    setName(name);

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin();
            it != attributes.end(); it++) {
        this->attributes.push_back(*it);
    }
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