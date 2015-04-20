#include "smt_logic.h"

using namespace smt;
using namespace std;

SmtLogic::SmtLogic(std::shared_ptr<Symbol> name) {
    setName(name);
}

SmtLogic::SmtLogic(std::shared_ptr<Symbol> name,
                   vector<shared_ptr<Attribute>> &attributes) {
    setName(name);

    for (vector<shared_ptr<Attribute>>::iterator it = attributes.begin();
         it != attributes.end(); it++) {
        this->attributes.push_back(*it);
    }
}

shared_ptr<Symbol> SmtLogic::getName() {
    return name;
}

void SmtLogic::setName(shared_ptr<Symbol> name) {
    this->name = name;
}

std::vector<shared_ptr<Attribute>> &SmtLogic::getAttributes() {
    return attributes;
}
