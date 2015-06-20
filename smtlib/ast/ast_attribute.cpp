#include <sstream>
#include "ast_attribute.h"

using namespace smtlib::ast;
using namespace std;

/* ==================================== Attribute ===================================== */

const shared_ptr<Keyword> Attribute::getKeyword() const {
    return keyword;
}

shared_ptr<Keyword> Attribute::getKeyword() {
    return keyword;
}

void Attribute::setKeyword(shared_ptr<Keyword> keyword) {
    this->keyword = keyword;
}

const shared_ptr<AttributeValue> Attribute::getValue() const {
    return value;
}

shared_ptr<AttributeValue> Attribute::getValue() {
    return value;
}

void Attribute::setValue(std::shared_ptr<AttributeValue> value) {
    this->value = value;
}

void Attribute::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string Attribute::toString() const {
    stringstream ss;
    ss << keyword->toString();
    if(value)
        ss << " " << value->toString();
    return ss.str();
}

/* ============================== CompoundAttributeValue ============================== */

CompoundAttributeValue::CompoundAttributeValue(const vector<shared_ptr<AttributeValue>> values) {
    this->values.insert(this->values.begin(), values.begin(), values.end());
}

const vector<shared_ptr<AttributeValue>> &CompoundAttributeValue::getValues() const {
    return values;
}

vector<shared_ptr<AttributeValue>> &CompoundAttributeValue::getValues() {
    return values;
}

void CompoundAttributeValue::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string CompoundAttributeValue::toString() const {
    stringstream ss;
    ss << "(";
    for(vector<shared_ptr<AttributeValue>>::const_iterator it = values.begin(); it != values.end(); it++) {
        ss << (*it)->toString();
        if(it + 1 != values.end())
            ss << " ";
    }
    ss << ")";
    return ss.str();
}