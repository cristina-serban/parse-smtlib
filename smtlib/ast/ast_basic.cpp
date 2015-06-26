#include "ast_basic.h"
#include <sstream>

using namespace smtlib::ast;
using namespace std;

/* ====================================== Symbol ====================================== */

void Symbol::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string Symbol::toString() {
    return value;
}

/* ====================================== Keyword ===================================== */

void Keyword::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string Keyword::toString() {
    return value;
}

/* ================================= MetaSpecConstant ================================= */

void MetaSpecConstant::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string MetaSpecConstant::toString() {
    return (type == Type::META_SPEC_STRING) ? "STRING"
                                            : (type == Type::META_SPEC_NUMERAL ? "NUMERAL"
                                                                               : "DECIMAL");
}

/* =================================== BooleanValue =================================== */

void BooleanValue::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string BooleanValue::toString() {
    if(value)
        return "true";
    else
        return "false";
}

/* =================================== PropLiteral ==================================== */

void PropLiteral::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string PropLiteral::toString() {
    if(negated) {
        stringstream ss;
        ss << "(not " << symbol->toString() << ")";
        return ss.str();
    } else {
        return symbol->toString();
    }
}