#include "ast_basic.h"
#include "../util/global_values.h"

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
    return (type == Type::META_SPEC_STRING) ? MSCONST_STRING
                                            : (type == Type::META_SPEC_NUMERAL ? MSCONST_NUMERAL
                                                                               : MSCONST_DECIMAL);
}

/* =================================== BooleanValue =================================== */

void BooleanValue::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string BooleanValue::toString() {
    if(value)
        return CONST_TRUE;
    else
        return CONST_FALSE;
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