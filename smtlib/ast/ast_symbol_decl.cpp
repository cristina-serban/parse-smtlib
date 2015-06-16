#include <sstream>
#include "ast_symbol_decl.h"

using namespace std;
using namespace smtlib::ast;

/* =============================== SortSymbolDeclaration ============================== */

SortSymbolDeclaration::SortSymbolDeclaration(shared_ptr<Identifier> identifier,
                                             std::shared_ptr<NumeralLiteral> arity,
                                             const vector<shared_ptr<Attribute>> &attributes)
        : identifier(identifier), arity(arity){
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

const shared_ptr<Identifier> SortSymbolDeclaration::getIdentifier() const {
    return identifier;
}

shared_ptr<Identifier> SortSymbolDeclaration::getIdentifier() {
    return identifier;
}

void SortSymbolDeclaration::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

const shared_ptr<NumeralLiteral> SortSymbolDeclaration::getArity() const {
    return arity;
}

shared_ptr<NumeralLiteral> SortSymbolDeclaration::getArity() {
    return arity;
}

void SortSymbolDeclaration::setArity(shared_ptr<NumeralLiteral> arity) {
    this->arity = arity;
}

const vector<shared_ptr<Attribute>> &SortSymbolDeclaration::getAttributes() const {
    return attributes;
}

vector<shared_ptr<Attribute>> &SortSymbolDeclaration::getAttributes() {
    return attributes;
}

void SortSymbolDeclaration::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
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
SpecConstFunDeclaration::SpecConstFunDeclaration(shared_ptr<SpecConstant> constant,
                                                 shared_ptr<Sort> sort,
                                                 const vector<shared_ptr<Attribute>> &attributes)
        : constant(constant), sort(sort) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

const shared_ptr<SpecConstant> SpecConstFunDeclaration::getConstant() const {
    return constant;
}

shared_ptr<SpecConstant> SpecConstFunDeclaration::getConstant() {
    return constant;
}

void SpecConstFunDeclaration::setConstant(shared_ptr<SpecConstant> constant) {
    this->constant = constant;
}

const shared_ptr<Sort> SpecConstFunDeclaration::getSort() const {
    return sort;
}

shared_ptr<Sort> SpecConstFunDeclaration::getSort() {
    return sort;
}

void SpecConstFunDeclaration::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

const vector<shared_ptr<Attribute>> &SpecConstFunDeclaration::getAttributes() const {
    return attributes;
}

vector<shared_ptr<Attribute>> &SpecConstFunDeclaration::getAttributes() {
    return attributes;
}

void SpecConstFunDeclaration::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
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

const shared_ptr<MetaSpecConstant> MetaSpecConstFunDeclaration::getConstant() const {
    return constant;
}

shared_ptr<MetaSpecConstant> MetaSpecConstFunDeclaration::getConstant() {
    return constant;
}

void MetaSpecConstFunDeclaration::setConstant(shared_ptr<MetaSpecConstant> constant) {
    this->constant = constant;
}

const shared_ptr<Sort> MetaSpecConstFunDeclaration::getSort() const {
    return sort;
}

shared_ptr<Sort> MetaSpecConstFunDeclaration::getSort() {
    return sort;
}

void MetaSpecConstFunDeclaration::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

const vector<shared_ptr<Attribute>> &MetaSpecConstFunDeclaration::getAttributes() const {
    return attributes;
}

vector<shared_ptr<Attribute>> &MetaSpecConstFunDeclaration::getAttributes() {
    return attributes;
}

void MetaSpecConstFunDeclaration::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
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

/* ============================== IdentifierFunDeclaration =============================== */

IdentifierFunDeclaration::IdentifierFunDeclaration(shared_ptr<Identifier> identifier,
                                             const vector<shared_ptr<Sort>> &signature)
        : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

IdentifierFunDeclaration::IdentifierFunDeclaration(shared_ptr<Identifier> identifier,
                                             const vector<shared_ptr<Sort>> &signature,
                                             const vector<shared_ptr<Attribute>> &attributes)
        : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());

}

const shared_ptr<Identifier> IdentifierFunDeclaration::getIdentifier() const{
    return identifier;
}

shared_ptr<Identifier> IdentifierFunDeclaration::getIdentifier() {
    return identifier;
}

void IdentifierFunDeclaration::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

const vector<shared_ptr<Sort>> &IdentifierFunDeclaration::getSignature() const {
    return signature;
}

vector<shared_ptr<Sort>> &IdentifierFunDeclaration::getSignature() {
    return signature;
}

const vector<shared_ptr<Attribute>> &IdentifierFunDeclaration::getAttributes() const {
    return attributes;
}

vector<shared_ptr<Attribute>> &IdentifierFunDeclaration::getAttributes() {
    return attributes;
}

void IdentifierFunDeclaration::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string IdentifierFunDeclaration::toString() {
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

/* =============================== ParametricFunDeclaration ================================ */

ParametricFunDeclaration::ParametricFunDeclaration(const vector<shared_ptr<Symbol>> &params,
                                         shared_ptr<Identifier> identifier,
                                         const vector<shared_ptr<Sort>> &signature) {
    this->params.insert(this->params.end(), params.begin(), params.end());
    setIdentifier(identifier);
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

ParametricFunDeclaration::ParametricFunDeclaration(const vector<shared_ptr<Symbol>> &params,
                                         shared_ptr<Identifier> identifier,
                                         const vector<shared_ptr<Sort>> &signature,
                                         const vector<shared_ptr<Attribute>> &attributes) {
    this->params.insert(this->params.end(), params.begin(), params.end());
    setIdentifier(identifier);
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

const vector<shared_ptr<Symbol>> &ParametricFunDeclaration::getParams() const {
    return params;
}

vector<shared_ptr<Symbol>> &ParametricFunDeclaration::getParams() {
    return params;
}

void ParametricFunDeclaration::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string ParametricFunDeclaration::toString() {
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