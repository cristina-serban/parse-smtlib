#include <sstream>
#include "smt_identifier.h"

using namespace std;
using namespace smt::ast;

/* ==================================== Identifier ==================================== */

Identifier::Identifier(shared_ptr<Symbol> symbol,
                       const vector<shared_ptr<IIndex>> indices)
        : symbol(symbol) {
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

string Identifier::toString() {
    if(!isIndexed())
        return symbol->toString();
    else {
        stringstream ss;
        ss << "( _ " << symbol->toString() << " ";
        for(vector<shared_ptr<IIndex>>::iterator it = indices.begin(); it != indices.end(); it++) {
            ss << (*it)->toString() << " ";
        }
        ss << ")";
        return ss.str();
    }
}

/* =============================== QualifiedIdentifier ================================ */

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

string QualifiedIdentifier::toString() {
    stringstream ss;
    ss << "( as " << identifier->toString() << " " << sort->toString() << " )";
    return ss.str();
}