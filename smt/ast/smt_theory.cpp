#include <memory>
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