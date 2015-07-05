#include "ast_symbol_decl.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* =============================== SortSymbolDeclaration ============================== */

SortSymbolDeclaration::SortSymbolDeclaration(shared_ptr<SimpleIdentifier> identifier,
                                             std::shared_ptr<NumeralLiteral> arity,
                                             vector<shared_ptr<Attribute>>& attributes)
        : identifier(identifier), arity(arity){
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
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
                                                 vector<shared_ptr<Attribute>>& attributes)
        : constant(constant), sort(sort) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
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
                                                         vector<shared_ptr<Attribute>>& attributes)
        : constant(constant), sort(sort) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
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
                                             vector<shared_ptr<Sort>>& signature)
        : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

SimpleFunDeclaration::SimpleFunDeclaration(shared_ptr<SimpleIdentifier> identifier,
                                             vector<shared_ptr<Sort>>& signature,
                                             vector<shared_ptr<Attribute>>& attributes)
        : identifier(identifier) {
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());

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

ParametricFunDeclaration::ParametricFunDeclaration(vector<shared_ptr<Symbol>>& params,
                                         shared_ptr<SimpleIdentifier> identifier,
                                         vector<shared_ptr<Sort>>& signature) {
    this->params.insert(this->params.end(), params.begin(), params.end());
    setIdentifier(identifier);
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
}

ParametricFunDeclaration::ParametricFunDeclaration(vector<shared_ptr<Symbol>>& params,
                                         shared_ptr<SimpleIdentifier> identifier,
                                         vector<shared_ptr<Sort>>& signature,
                                         vector<shared_ptr<Attribute>>& attributes) {
    this->params.insert(this->params.end(), params.begin(), params.end());
    setIdentifier(identifier);
    this->signature.insert(this->signature.end(), signature.begin(), signature.end());
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
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