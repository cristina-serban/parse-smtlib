#include "smt_attribute.h"

using namespace smt;
using namespace std;

Attribute::Attribute(shared_ptr<Keyword> keyword) {
    setKeyword(keyword);
}

Attribute::Attribute(shared_ptr<Keyword> keyword,
                     shared_ptr<IAttributeValue> value) {
    setKeyword(keyword);
    setValue(value);
}

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


