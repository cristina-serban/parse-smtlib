#include "smt_attribute.h"

using namespace smt::ast;
using namespace std;

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