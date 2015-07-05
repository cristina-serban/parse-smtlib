#include "ast_var.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================== SortedVariable ================================== */
void SortedVariable::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string SortedVariable::toString() {
    stringstream ss;
    ss << symbol->toString() << " " << sort->toString();
    return ss.str();
}

/* ==================================== VarBinding ==================================== */
void VarBinding::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string VarBinding::toString() {
    stringstream ss;
    ss << symbol->toString() << " (" << term->toString() << ")";
    return ss.str();
}