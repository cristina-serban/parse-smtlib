#include <sstream>
#include "ast_basic.h"

using namespace smtlib::ast;
using namespace std;

/* ====================================== Symbol ====================================== */

const string &Symbol::getValue() const {
    return value;
}

string &Symbol::getValue() {
    return value;
}

void Symbol::setValue(string value) {
    this->value = value;
}

void Symbol::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string Symbol::toString() const {
    return value;
}

/* ====================================== Keyword ===================================== */

const string &Keyword::getValue() const {
    return value;
}

string &Keyword::getValue() {
    return value;
}

void Keyword::setValue(string value) {
    this->value = value;
}

void Keyword::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string Keyword::toString() const {
    return value;
}

/* ================================= MetaSpecConstant ================================= */

MetaSpecConstant::Type MetaSpecConstant::getType() const {
    return type;
}

void MetaSpecConstant::setType(MetaSpecConstant::Type type) {
    this->type = type;
}

void MetaSpecConstant::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string MetaSpecConstant::toString() const {
    return (type == Type::META_SPEC_STRING) ? "STRING"
                                            : (type == Type::META_SPEC_NUMERAL ? "NUMERAL"
                                                                               : "DECIMAL");
}

/* =================================== BooleanValue =================================== */

bool BooleanValue::getValue() const {
    return value;
}

void BooleanValue::setValue(bool value) {
    this->value = value;
}

void BooleanValue::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string BooleanValue::toString() const {
    if(value)
        return "true";
    else
        return "false";
}

/* =================================== PropLiteral ==================================== */

const shared_ptr<Symbol> PropLiteral::getSymbol() const {
    return symbol;
}

shared_ptr<Symbol> PropLiteral::getSymbol() {
    return symbol;
}

void PropLiteral::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

bool PropLiteral::isNegated() const {
    return negated;
}

void PropLiteral::setNegated(bool negated) {
    this->negated = negated;
}

void PropLiteral::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string PropLiteral::toString() const {
    if(negated) {
        stringstream ss;
        ss << "(not " << symbol->toString() << ")";
        return ss.str();
    } else {
        return symbol->toString();
    }
}