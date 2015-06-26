#include "ast_var.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================== SortedVariable ================================== */

shared_ptr<Symbol> SortedVariable::getSymbol() {
    return symbol;
}

void SortedVariable::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

shared_ptr<Sort> SortedVariable::getSort() {
    return sort;
}

void SortedVariable::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

void SortedVariable::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string SortedVariable::toString() {
    stringstream ss;
    ss << symbol->toString() << " " << sort->toString();
    return ss.str();
}

/* ==================================== VarBinding ==================================== */

shared_ptr<Symbol> VarBinding::getSymbol() {
    return symbol;
}

void VarBinding::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

shared_ptr<Term> VarBinding::getTerm() {
    return term;
}

void VarBinding::setTerm(shared_ptr<Term> term) {
    this->term = term;
}

void VarBinding::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string VarBinding::toString() {
    stringstream ss;
    ss << symbol->toString() << " (" << term->toString() << ")";
    return ss.str();
}