#include "smt_identifier.h"

using namespace std;
using namespace smt;

/* ==================================== Identifier ==================================== */

Identifier::Identifier(std::shared_ptr<Symbol> symbol) {
    setSymbol(symbol);
}

Identifier::Identifier(std::shared_ptr<Symbol> symbol,
                       std::vector<std::shared_ptr<IIndex>> indices) {
    setSymbol(symbol);

    for (std::vector<std::shared_ptr<IIndex>>::iterator it = indices.begin(); it != indices.end(); it++) {
        indices.push_back(*it);
    }
}

std::shared_ptr<Symbol> Identifier::getSymbol() {
    return symbol;
}

void Identifier::setSymbol(std::shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

std::vector<std::shared_ptr<IIndex>> &Identifier::getIndices() {
    return indices;
}

bool Identifier::isIndexed() {
    return !indices.empty();
}

/* =============================== QualifiedIdentifier ================================ */

QualifiedIdentifier::QualifiedIdentifier(std::shared_ptr<Identifier> identifier,
                                         std::shared_ptr<Sort> sort) {
    setIdentifier(identifier);
    setSort(sort);
}

std::shared_ptr<Identifier> QualifiedIdentifier::getIdentifier() {
    return identifier;
}

void QualifiedIdentifier::setIdentifier(std::shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

std::shared_ptr<Sort> QualifiedIdentifier::getSort() {
    return sort;
}

void QualifiedIdentifier::setSort(std::shared_ptr<Sort> sort) {
    this->sort = sort;
}