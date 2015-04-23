#include "smt_var.h"

using namespace std;
using namespace smt::ast;

/* ================================== SortedVariable ================================== */

SortedVariable::SortedVariable(shared_ptr<Symbol> symbol,
                               shared_ptr<Sort> sort) {
    setSymbol(symbol);
    setSort(sort);
}

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

/* ==================================== VarBinding ==================================== */

VarBinding::VarBinding(shared_ptr<Symbol> symbol,
                       shared_ptr<ITerm> term) {
    setSymbol(symbol);
    setTerm(term);
}

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