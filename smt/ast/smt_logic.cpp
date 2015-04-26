#include <sstream>
#include "smt_logic.h"

using namespace smt::ast;
using namespace std;

SmtLogic::SmtLogic(std::shared_ptr<Symbol> name,
                   const vector<shared_ptr<Attribute>> &attributes)
        : name(name) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
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

string SmtLogic::toString() {
    stringstream ss;
    ss << "( logic  ";

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";
    return ss.str();
}