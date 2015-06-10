#include <sstream>
#include "smt_logic.h"

using namespace smtlib::ast;
using namespace std;

Logic::Logic(std::shared_ptr<Symbol> name,
                   const vector<shared_ptr<Attribute>> &attributes)
        : name(name) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

shared_ptr<Symbol> Logic::getName() {
    return name;
}

void Logic::setName(shared_ptr<Symbol> name) {
    this->name = name;
}

std::vector<shared_ptr<Attribute>> &Logic::getAttributes() {
    return attributes;
}

void Logic::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string Logic::toString() {
    stringstream ss;
    ss << "( logic  " << name->toString() << " ";

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";
    return ss.str();
}