#include "smt_symbol_decl.h"

using namespace std;
using namespace smt;

/* =============================== SortSymbolDeclaration ============================== */

SortSymbolDeclaration::SortSymbolDeclaration(shared_ptr<Identifier> identifier,
                                             long cardinality) {
    setIdentifier(identifier);
    setCardinality(cardinality);
}

SortSymbolDeclaration::SortSymbolDeclaration(shared_ptr<Identifier> identifier,
                                             long cardinality,
                                             vector<shared_ptr<Attribute>> &attributes) {
    setIdentifier(identifier);
    setCardinality(cardinality);

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        this->attributes.push_back(*it);
    }
}

shared_ptr<Identifier> SortSymbolDeclaration::getIdentifier() {
    return identifier;
}

void SortSymbolDeclaration::setIdentifier(shared_ptr<Identifier> identifier) {
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

/* ============================= SpecConstFunDeclaration ============================== */

SpecConstFunDeclaration::SpecConstFunDeclaration(shared_ptr<ISpecConstant> constant,
                                                 shared_ptr<Sort> sort) {
    setConstant(constant);
    setSort(sort);
}

SpecConstFunDeclaration::SpecConstFunDeclaration(shared_ptr<ISpecConstant> constant,
                                                 shared_ptr<Sort> sort,
                                                 vector<shared_ptr<Attribute>> &attributes) {
    setConstant(constant);
    setSort(sort);

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        this->attributes.push_back(*it);
    }
}

shared_ptr<ISpecConstant> SpecConstFunDeclaration::getConstant() {
    return constant;
}

void SpecConstFunDeclaration::setConstant(shared_ptr<ISpecConstant> constant) {
    this->constant = constant;
}

shared_ptr<Sort> SpecConstFunDeclaration::getSort() {
    return sort;
}

void SpecConstFunDeclaration::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

vector<shared_ptr<Attribute>> &SpecConstFunDeclaration::getAttributes() {
    return attributes;
}

/* ========================== MetaSpecConstFunDeclaration =========================== */

MetaSpecConstFunDeclaration::MetaSpecConstFunDeclaration(shared_ptr<MetaSpecConstant> constant,
                                                         shared_ptr<Sort> sort) {
    setConstant(constant);
    setSort(sort);
}

MetaSpecConstFunDeclaration::MetaSpecConstFunDeclaration(shared_ptr<MetaSpecConstant> constant,
                                                         shared_ptr<Sort> sort,
                                                         vector<shared_ptr<Attribute>> &attributes) {
    setConstant(constant);
    setSort(sort);

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        this->attributes.push_back(*it);
    }
}

shared_ptr<MetaSpecConstant> MetaSpecConstFunDeclaration::getConstant() {
    return constant;
}

void MetaSpecConstFunDeclaration::setConstant(shared_ptr<MetaSpecConstant> constant) {
    this->constant = constant;
}

shared_ptr<Sort> MetaSpecConstFunDeclaration::getSort() {
    return sort;
}

void MetaSpecConstFunDeclaration::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

vector<shared_ptr<Attribute>> &MetaSpecConstFunDeclaration::getAttributes() {
    return attributes;
}

/* ============================== IdentifFunDeclaration =============================== */

IdentifFunDeclaration::IdentifFunDeclaration(shared_ptr<Identifier> identifier,
                                             vector<shared_ptr<Sort>> &signature) {
    setIdentifier(identifier);

    for(vector<shared_ptr<Sort>>::iterator it = signature.begin(); it != signature.end(); it++) {
        this->signature.push_back(*it);
    }
}

IdentifFunDeclaration::IdentifFunDeclaration(shared_ptr<Identifier> identifier,
                                             vector<shared_ptr<Sort>> &signature,
                                             vector<shared_ptr<Attribute>> &attributes) {
    setIdentifier(identifier);

    for(vector<shared_ptr<Sort>>::iterator it = signature.begin(); it != signature.end(); it++) {
        this->signature.push_back(*it);
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        this->attributes.push_back(*it);
    }
}

shared_ptr<Identifier> IdentifFunDeclaration::getIdentifier() {
    return identifier;
}

void IdentifFunDeclaration::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

vector<shared_ptr<Sort>> &IdentifFunDeclaration::getSignature() {
    return signature;
}

vector<shared_ptr<Attribute>> &IdentifFunDeclaration::getAttributes() {
    return attributes;
}

/* =============================== ParamFunDeclaration ================================ */

ParamFunDeclaration::ParamFunDeclaration(vector<shared_ptr<Symbol>> &params,
                                         shared_ptr<Identifier> identifier,
                                         vector<shared_ptr<Sort>> &signature) {
    for(vector<shared_ptr<Symbol>>::iterator it = params.begin(); it != params.end(); it++) {
        this->params.push_back(*it);
    }

    setIdentifier(identifier);

    for(vector<shared_ptr<Sort>>::iterator it = signature.begin(); it != signature.end(); it++) {
        this->signature.push_back(*it);
    }
}

ParamFunDeclaration::ParamFunDeclaration(vector<shared_ptr<Symbol>> &params,
                                         shared_ptr<Identifier> identifier,
                                         vector<shared_ptr<Sort>> &signature,
                                         vector<shared_ptr<Attribute>> &attributes) {
    for(vector<shared_ptr<Symbol>>::iterator it = params.begin(); it != params.end(); it++) {
        this->params.push_back(*it);
    }

    setIdentifier(identifier);

    for(vector<shared_ptr<Sort>>::iterator it = signature.begin(); it != signature.end(); it++) {
        this->signature.push_back(*it);
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        this->attributes.push_back(*it);
    }
}

vector<shared_ptr<Symbol>> &ParamFunDeclaration::getParams() {
    return params;
}