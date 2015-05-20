#include <sstream>
#include "smt_symbol_decl.h"

using namespace std;
using namespace smtlib::ast;

/* =============================== SortSymbolDeclaration ============================== */

SortSymbolDeclaration::SortSymbolDeclaration(shared_ptr<Identifier> identifier,
                                             std::shared_ptr<NumeralLiteral> arity,
                                             const vector<shared_ptr<Attribute>> &attributes)
        : identifier(identifier), arity(arity){
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

shared_ptr<Identifier> SortSymbolDeclaration::getIdentifier() {
    return identifier;
}

void SortSymbolDeclaration::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

shared_ptr<NumeralLiteral> SortSymbolDeclaration::getArity() {
    return arity;
}

void SortSymbolDeclaration::setArity(shared_ptr<NumeralLiteral> arity) {
    this->arity = arity;
}

vector<shared_ptr<Attribute>> &SortSymbolDeclaration::getAttributes() {
    return attributes;
}

string SortSymbolDeclaration::toString() {
    stringstream ss;
    ss << "( " << identifier->toString() << " " << arity->toString() << " ";

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";

    return ss.str();
}

/* ============================= SpecConstFunDeclaration ============================== */
SpecConstFunDeclaration::SpecConstFunDeclaration(shared_ptr<ISpecConstant> constant,
                                                 shared_ptr<Sort> sort,
                                                 const vector<shared_ptr<Attribute>> &attributes)
        : constant(constant), sort(sort) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
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

string SpecConstFunDeclaration::toString() {
    stringstream ss;
    ss << "( " << constant->toString() << " " << sort->toString() << " ";

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";

    return ss.str();
}

/* ========================== MetaSpecConstFunDeclaration =========================== */

MetaSpecConstFunDeclaration::MetaSpecConstFunDeclaration(shared_ptr<MetaSpecConstant> constant,
                                                         shared_ptr<Sort> sort,
                                                         const vector<shared_ptr<Attribute>> &attributes)
        : constant(constant), sort(sort) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
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

string MetaSpecConstFunDeclaration::toString() {
    stringstream ss;
    ss << "( " << constant->toString() << " " << sort->toString() << " ";

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";

    return ss.str();
}

/* ============================== IdentifFunDeclaration =============================== */

IdentifFunDeclaration::IdentifFunDeclaration(shared_ptr<Identifier> identifier,
                                             const vector<shared_ptr<Sort>> &signature)
        : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

IdentifFunDeclaration::IdentifFunDeclaration(shared_ptr<Identifier> identifier,
                                             const vector<shared_ptr<Sort>> &signature,
                                             const vector<shared_ptr<Attribute>> &attributes)
        : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());

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

string IdentifFunDeclaration::toString() {
    stringstream ss;
    ss << "( " << identifier->toString() << " ";

    for(vector<shared_ptr<Sort>>::iterator it = signature.begin(); it != signature.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";

    return ss.str();
}

/* =============================== ParamFunDeclaration ================================ */

ParamFunDeclaration::ParamFunDeclaration(const vector<shared_ptr<Symbol>> &params,
                                         shared_ptr<Identifier> identifier,
                                         const vector<shared_ptr<Sort>> &signature) {
    this->params.insert(this->params.end(), params.begin(), params.end());
    setIdentifier(identifier);
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

ParamFunDeclaration::ParamFunDeclaration(const vector<shared_ptr<Symbol>> &params,
                                         shared_ptr<Identifier> identifier,
                                         const vector<shared_ptr<Sort>> &signature,
                                         const vector<shared_ptr<Attribute>> &attributes) {
    this->params.insert(this->params.end(), params.begin(), params.end());
    setIdentifier(identifier);
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

vector<shared_ptr<Symbol>> &ParamFunDeclaration::getParams() {
    return params;
}

string ParamFunDeclaration::toString() {
    stringstream ss;
    ss << "( par ( ";
    for(vector<shared_ptr<Symbol>>::iterator it = params.begin(); it != params.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ") ( " << identifier->toString() << " ";
    for(vector<shared_ptr<Sort>>::iterator it = signature.begin(); it != signature.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ") )";

    return ss.str();
}