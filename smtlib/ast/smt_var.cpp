#include <sstream>
#include "smt_var.h"

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

shared_ptr<ITerm> VarBinding::getTerm() {
    return term;
}

void VarBinding::setTerm(shared_ptr<ITerm> term) {
    this->term = term;
}

string VarBinding::toString() {
    stringstream ss;
    ss << symbol->toString() << " (" << term->toString() << ")";
    return ss.str();
}