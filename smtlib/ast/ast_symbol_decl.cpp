#include "ast_symbol_decl.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* =============================== SortSymbolDeclaration ============================== */

SortSymbolDeclaration::SortSymbolDeclaration(shared_ptr<SimpleIdentifier> identifier,
                                             std::shared_ptr<NumeralLiteral> arity,
                                             vector<shared_ptr<Attribute>> &attributes)
        : identifier(identifier), arity(arity){
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

shared_ptr<SimpleIdentifier> SortSymbolDeclaration::getIdentifier() {
    return identifier;
}

void SortSymbolDeclaration::setIdentifier(shared_ptr<SimpleIdentifier> identifier) {
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

void SortSymbolDeclaration::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string SortSymbolDeclaration::toString() {
    stringstream ss;
    ss << "(" << identifier->toString() << " " << arity->toString();

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
         ss << " " << (*it)->toString();
    }

    ss << ")";

    return ss.str();
}

/* ============================= SpecConstFunDeclaration ============================== */
SpecConstFunDeclaration::SpecConstFunDeclaration(shared_ptr<SpecConstant> constant,
                                                 shared_ptr<Sort> sort,
                                                 vector<shared_ptr<Attribute>> &attributes)
        : constant(constant), sort(sort) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

shared_ptr<SpecConstant> SpecConstFunDeclaration::getConstant() {
    return constant;
}

void SpecConstFunDeclaration::setConstant(shared_ptr<SpecConstant> constant) {
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

void SpecConstFunDeclaration::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string SpecConstFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << constant->toString() << " " << sort->toString();

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << " " << (*it)->toString();
    }

    ss << ")";

    return ss.str();
}

/* ========================== MetaSpecConstFunDeclaration =========================== */

MetaSpecConstFunDeclaration::MetaSpecConstFunDeclaration(shared_ptr<MetaSpecConstant> constant,
                                                         shared_ptr<Sort> sort,
                                                         vector<shared_ptr<Attribute>> &attributes)
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

void MetaSpecConstFunDeclaration::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string MetaSpecConstFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << constant->toString() << " " << sort->toString();

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << " " << (*it)->toString();
    }

    ss << ")";

    return ss.str();
}

/* ============================== SimpleFunDeclaration =============================== */

SimpleFunDeclaration::SimpleFunDeclaration(shared_ptr<SimpleIdentifier> identifier,
                                             vector<shared_ptr<Sort>> &signature)
        : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

SimpleFunDeclaration::SimpleFunDeclaration(shared_ptr<SimpleIdentifier> identifier,
                                             vector<shared_ptr<Sort>> &signature,
                                             vector<shared_ptr<Attribute>> &attributes)
        : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());

}

shared_ptr<SimpleIdentifier> SimpleFunDeclaration::getIdentifier() {
    return identifier;
}

void SimpleFunDeclaration::setIdentifier(shared_ptr<SimpleIdentifier> identifier) {
    this->identifier = identifier;
}

vector<shared_ptr<Sort>> & SimpleFunDeclaration::getSignature() {
    return signature;
}

vector<shared_ptr<Attribute>> & SimpleFunDeclaration::getAttributes() {
    return attributes;
}

void SimpleFunDeclaration::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string SimpleFunDeclaration::toString() {
    stringstream ss;
    ss << "(" << identifier->toString();

    for(vector<shared_ptr<Sort>>::iterator it = signature.begin(); it != signature.end(); it++) {
        ss << " " << (*it)->toString();
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << " " << (*it)->toString();
    }

    ss << ")";

    return ss.str();
}

/* =============================== ParametricFunDeclaration ================================ */

ParametricFunDeclaration::ParametricFunDeclaration(vector<shared_ptr<Symbol>> &params,
                                         shared_ptr<SimpleIdentifier> identifier,
                                         vector<shared_ptr<Sort>> &signature) {
    this->params.insert(this->params.end(), params.begin(), params.end());
    setIdentifier(identifier);
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

ParametricFunDeclaration::ParametricFunDeclaration(vector<shared_ptr<Symbol>> &params,
                                         shared_ptr<SimpleIdentifier> identifier,
                                         vector<shared_ptr<Sort>> &signature,
                                         vector<shared_ptr<Attribute>> &attributes) {
    this->params.insert(this->params.end(), params.begin(), params.end());
    setIdentifier(identifier);
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

vector<shared_ptr<Symbol>> &ParametricFunDeclaration::getParams() {
    return params;
}

shared_ptr<SimpleIdentifier> ParametricFunDeclaration::getIdentifier() {
    return identifier;
}

void ParametricFunDeclaration::setIdentifier(shared_ptr<SimpleIdentifier> identifier) {
    this->identifier = identifier;
}

vector<shared_ptr<Sort>> &ParametricFunDeclaration::getSignature() {
    return signature;
}

vector<shared_ptr<Attribute>> &ParametricFunDeclaration::getAttributes() {
    return attributes;
}

void ParametricFunDeclaration::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string ParametricFunDeclaration::toString() {
    stringstream ss;
    ss << "(par (";
    for(vector<shared_ptr<Symbol>>::iterator it = params.begin(); it != params.end(); it++) {
        if(it != params.begin())
            ss << " ";
        ss << (*it)->toString();
    }

    ss << ") (" << identifier->toString();
    for(vector<shared_ptr<Sort>>::iterator it = signature.begin(); it != signature.end(); it++) {
        ss << " " << (*it)->toString();
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        ss << " " << (*it)->toString();
    }

    ss << "))";

    return ss.str();
}