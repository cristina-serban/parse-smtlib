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
    this->type = type;
}

MetaSpecConstant::Type MetaSpecConstant::getType() {
    return type;
}

void MetaSpecConstant::setType(MetaSpecConstant::Type type) {
    this->type = type;
}

/* =================================== BooleanValue =================================== */

BooleanValue::BooleanValue(BooleanValue::Type type) {
    this->type = type;
}

BooleanValue::Type BooleanValue::getType() {
    return type;
}

void BooleanValue::setType(BooleanValue::Type type) {
    this->type = type;
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