#include "ast_attribute.h"
#include <sstream>

using namespace smtlib::ast;
using namespace std;

/* ==================================== Attribute ===================================== */

void Attribute::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string Attribute::toString() {
    stringstream ss;
    ss << keyword->toString();
    if(value)
        ss << " " << value->toString();
    return ss.str();
}

/* ============================== CompAttributeValue ============================== */

CompAttributeValue::CompAttributeValue(vector<shared_ptr<AttributeValue>> values) {
    this->values.insert(this->values.begin(), values.begin(), values.end());
}

void CompAttributeValue::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string CompAttributeValue::toString() {
    stringstream ss;
    ss << "(";
    for(vector<shared_ptr<AttributeValue>>::iterator it = values.begin(); it != values.end(); it++) {
        ss << (*it)->toString();
        if(it + 1 != values.end())
            ss << " ";
    }
    ss << ")";
    return ss.str();
}