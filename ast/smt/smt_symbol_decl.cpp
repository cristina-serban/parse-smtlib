//
// Created by cristinaserban on 17.04.2015.
//

#include "smt_symbol_decl.h"

using namespace std;
using namespace smt;

SortSymbolDeclaration::SortSymbolDeclaration(shared_ptr<IIdentifier> identifier,
                                             long cardinality) {
    setIdentifier(identifier);
    setCardinality(cardinality);
}

SortSymbolDeclaration::SortSymbolDeclaration(shared_ptr<IIdentifier> identifier,
                                             long cardinality,
                                             vector<shared_ptr<Attribute>> &attributes) {
    setIdentifier(identifier);
    setCardinality(cardinality);

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        attributes.push_back(*it);
    }
}

shared_ptr<IIdentifier> &SortSymbolDeclaration::getIdentifier() {
    return identifier;
}

void SortSymbolDeclaration::setIdentifier(shared_ptr<IIdentifier> identifier) {
    this->identifier = identifier;
}

long SortSymbolDeclaration::getCardinality() {
    return cardinality;
}

void SortSymbolDeclaration::setCardinality(long cardinality) {
    this->cardinality = cardinality;
}

vector<shared_ptr<Attribute>> &SortSymbolDeclaration::getAttributes() {
    return attributes;
}