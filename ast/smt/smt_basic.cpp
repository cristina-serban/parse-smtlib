#include "smt_basic.h"

using namespace smt;
using namespace std;

/* ====================================== Symbol ====================================== */

Symbol::Symbol(string value) {
    this->value = value;
}

string Symbol::getValue() {
    return value;
}

void Symbol::setValue(string value) {
    this->value = value;
}

/* ====================================== Keyword ===================================== */

Keyword::Keyword(string value) {
    this->value = value;
}

string Keyword::getValue() {
    return value;
}

void Keyword::setValue(string value) {
    this->value = value;
}

/* ================================= MetaSpecConstant ================================= */

MetaSpecConstant::MetaSpecConstant(MetaSpecConstant::Type type) {
    setType(type);
}

MetaSpecConstant::Type MetaSpecConstant::getType() {
    return type;
}

void MetaSpecConstant::setType(MetaSpecConstant::Type type) {
    this->type = type;
}

/* =================================== BooleanValue =================================== */

BooleanValue::BooleanValue(bool value) {
    setValue(value);
}

bool BooleanValue::getValue() {
    return value;
}

void BooleanValue::setValue(bool value) {
    this->value = value;
}

/* =================================== PropLiteral ==================================== */

PropLiteral::PropLiteral(std::shared_ptr<Symbol> symbol, bool negated) {
    setSymbol(symbol);
    setNegated(negated);
}

std::shared_ptr<Symbol> PropLiteral::getSymbol() {
    return symbol;
}

void PropLiteral::setSymbol(std::shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

bool PropLiteral::isNegated() {
    return negated;
}

void PropLiteral::setNegated(bool negated) {
    this->negated = negated;
}