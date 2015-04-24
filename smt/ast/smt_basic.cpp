#include "smt_basic.h"

using namespace smt::ast;
using namespace std;

/* ====================================== Symbol ====================================== */

string Symbol::getValue() {
    return value;
}

void Symbol::setValue(string value) {
    this->value = value;
}

/* ====================================== Keyword ===================================== */

string Keyword::getValue() {
    return value;
}

void Keyword::setValue(string value) {
    this->value = value;
}

/* ================================= MetaSpecConstant ================================= */

MetaSpecConstant::Type MetaSpecConstant::getType() {
    return type;
}

void MetaSpecConstant::setType(MetaSpecConstant::Type type) {
    this->type = type;
}

/* =================================== BooleanValue =================================== */

bool BooleanValue::getValue() {
    return value;
}

void BooleanValue::setValue(bool value) {
    this->value = value;
}

/* =================================== PropLiteral ==================================== */

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