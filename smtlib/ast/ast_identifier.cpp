#include <sstream>
#include "ast_identifier.h"

using namespace std;
using namespace smtlib::ast;

/* ==================================== Identifier ==================================== */

Identifier::Identifier(shared_ptr<Symbol> symbol,
                       const vector<shared_ptr<Index>> indices)
        : symbol(symbol) {
    this->indices.insert(this->indices.end(), indices.begin(), indices.end());
}

shared_ptr<Symbol> Identifier::getSymbol() const {
    return symbol;
}

void Identifier::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

vector<shared_ptr<Index>> &Identifier::getIndices() {
    return indices;
}

vector<shared_ptr<Index>> Identifier::getIndices() const {
    return indices;
}

bool Identifier::isIndexed() const {
    return !indices.empty();
}

void Identifier::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string Identifier::toString() {
    if(!isIndexed())
        return symbol->toString();
    else {
        stringstream ss;
        ss << "( _ " << symbol->toString() << " ";
        for(vector<shared_ptr<Index>>::iterator it = indices.begin(); it != indices.end(); it++) {
            ss << (*it)->toString() << " ";
        }
        ss << ")";
        return ss.str();
    }
}

/* =============================== QualifiedIdentifier ================================ */

shared_ptr<Identifier> QualifiedIdentifier::getIdentifier() const {
    return identifier;
}

void QualifiedIdentifier::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

shared_ptr<Sort> QualifiedIdentifier::getSort() const {
    return sort;
}

void QualifiedIdentifier::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

void QualifiedIdentifier::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string QualifiedIdentifier::toString() {
    stringstream ss;
    ss << "( as " << identifier->toString() << " " << sort->toString() << " )";
    return ss.str();
}