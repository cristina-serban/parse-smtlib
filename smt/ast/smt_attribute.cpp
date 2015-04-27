#include <sstream>
#include "smt_attribute.h"

using namespace smt::ast;
using namespace std;

/* ==================================== Attribute ===================================== */

shared_ptr<Keyword> Attribute::getKeyword() {
    return keyword;
}

void Attribute::setKeyword(shared_ptr<Keyword> keyword) {
    this->keyword = keyword;
}

shared_ptr<IAttributeValue> Attribute::getValue() {
    return value;
}

void Attribute::setValue(std::shared_ptr<IAttributeValue> value) {
    this->value = value;
}

string Attribute::toString() {
    stringstream ss;
    ss << keyword->toString();
    if(value)
        ss << " " << value->toString();
    return ss.str();
}

/* ============================== CompoundAttributeValue ============================== */

CompoundAttributeValue::CompoundAttributeValue(const vector<shared_ptr<IAttributeValue>> values) {
    this->values.insert(this->values.begin(), values.begin(), values.end());
}

vector<shared_ptr<IAttributeValue>> &CompoundAttributeValue::getValues() {
    return values;
}

string CompoundAttributeValue::toString() {
    stringstream ss;
    for(vector<shared_ptr<IAttributeValue>>::iterator it = values.begin(); it != values.end(); it++) {
        ss << (*it)->toString() << " ";
    }
    return ss.str();
}