#include <sstream>
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

string Symbol::toString() {
    return value;
}

/* ====================================== Keyword ===================================== */

string Keyword::getValue() {
    return value;
}

void Keyword::setValue(string value) {
    this->value = value;
}

string Keyword::toString() {
    return value;
}

/* ================================= MetaSpecConstant ================================= */

MetaSpecConstant::Type MetaSpecConstant::getType() {
    return type;
}

void MetaSpecConstant::setType(MetaSpecConstant::Type type) {
    this->type = type;
}

string MetaSpecConstant::toString() {
    return (type == Type::META_SPEC_STRING) ? "STRING"
                                            : (type == Type::META_SPEC_NUMERAL ? "NUMERAL"
                                                                               : "DECIMAL");
}

/* =================================== BooleanValue =================================== */

bool BooleanValue::getValue() {
    return value;
}

void BooleanValue::setValue(bool value) {
    this->value = value;
}

string BooleanValue::toString() {
    if(value)
        return "true";
    else
        return "false";
}

/* =================================== PropLiteral ==================================== */

shared_ptr<Symbol> PropLiteral::getSymbol() {
    return symbol;
}

void PropLiteral::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

bool PropLiteral::isNegated() {
    return negated;
}

void PropLiteral::setNegated(bool negated) {
    this->negated = negated;
}

string PropLiteral::toString() {
    if(negated) {
        stringstream ss;
        ss << "( not " << symbol->toString() << " )";
        return ss.str();
    } else {
        return symbol->toString();
    }
}