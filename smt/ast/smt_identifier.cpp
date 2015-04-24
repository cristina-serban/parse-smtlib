#include "smt_identifier.h"

using namespace std;
using namespace smt::ast;

/* ==================================== Identifier ==================================== */

Identifier::Identifier(shared_ptr<Symbol> symbol) {
    setSymbol(symbol);
}

Identifier::Identifier(shared_ptr<Symbol> symbol,
                       const vector<shared_ptr<IIndex>> indices) {
    setSymbol(symbol);
    this->indices.insert(this->indices.end(), indices.begin(), indices.end());
}

shared_ptr<Symbol> Identifier::getSymbol() {
    return symbol;
}

void Identifier::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

vector<shared_ptr<IIndex>> &Identifier::getIndices() {
    return indices;
}

bool Identifier::isIndexed() {
    return !indices.empty();
}

/* =============================== QualifiedIdentifier ================================ */

QualifiedIdentifier::QualifiedIdentifier(shared_ptr<Identifier> identifier,
                                         shared_ptr<Sort> sort) {
    setIdentifier(identifier);
    setSort(sort);
}

shared_ptr<Identifier> QualifiedIdentifier::getIdentifier() {
    return identifier;
}

void QualifiedIdentifier::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

shared_ptr<Sort> QualifiedIdentifier::getSort() {
    return sort;
}

void QualifiedIdentifier::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}