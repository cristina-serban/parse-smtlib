#include "ast_term.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================== QualifiedTerm =================================== */

QualifiedTerm::QualifiedTerm(shared_ptr<QIdentifier> identifier,
                             vector<shared_ptr<Term>> &terms)
        : identifier(identifier) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

shared_ptr<QIdentifier> QualifiedTerm::getIdentifier() {
    return identifier;
}

void QualifiedTerm::setIdentifier(shared_ptr<QIdentifier> identifier) {
    this->identifier = identifier;
}

vector<shared_ptr<Term>> &QualifiedTerm::getTerms() {
    return terms;
}

void QualifiedTerm::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string QualifiedTerm::toString() {
    stringstream ss;
    ss << "(" << identifier->toString() << " ";

    for(vector<shared_ptr<Term>>::iterator it = terms.begin(); it != terms.end(); it++) {
        if(it != terms.begin())
            ss << " ";
        ss << (*it)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== LetTerm ====================================== */

LetTerm::LetTerm(vector<shared_ptr<VarBinding>> &bindings,
                 shared_ptr<Term> term)
        : term(term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

shared_ptr<Term> LetTerm::getTerm() {
    return term;
}

void LetTerm::setTerm(shared_ptr<Term> term) {
    this->term = term;
}

vector<shared_ptr<VarBinding>> &LetTerm::getBindings() {
    return bindings;
}

void LetTerm::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string LetTerm::toString() {
    stringstream ss;
    ss << "(let (";

    for(vector<shared_ptr<VarBinding>>::iterator it = bindings.begin(); it != bindings.end(); it++) {
        if(it != bindings.begin())
            ss << " ";
        ss << "(" << (*it)->toString() << ")";
    }

    ss << ") " << term->toString() << ")";

    return ss.str();
}

/* ==================================== ForallTerm ==================================== */
ForallTerm::ForallTerm(vector<shared_ptr<SortedVariable>> &bindings,
                       shared_ptr<Term> term)
        : term(term)  {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

shared_ptr<Term> ForallTerm::getTerm() {
    return term;
}

void ForallTerm::setTerm(shared_ptr<Term> term) {
    this->term = term;
}

vector<shared_ptr<SortedVariable>> & ForallTerm::getBindings() {
    return bindings;
}

void ForallTerm::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string ForallTerm::toString() {
    stringstream ss;
    ss << "(forall (";

    for(vector<shared_ptr<SortedVariable>>::iterator it = bindings.begin(); it != bindings.end(); it++) {
        if(it != bindings.begin())
            ss << " ";
        ss << "(" << (*it)->toString() << ")";
    }

    ss << ") " << term->toString() << ")";

    return ss.str();
}

/* ==================================== ExistsTerm ==================================== */
ExistsTerm::ExistsTerm(vector<shared_ptr<SortedVariable>> &bindings,
                       shared_ptr<Term> term)
        : term(term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

shared_ptr<Term> ExistsTerm::getTerm() {
    return term;
}

void ExistsTerm::setTerm(shared_ptr<Term> term) {
    this->term = term;
}

vector<shared_ptr<SortedVariable>> &ExistsTerm::getBindings() {
    return bindings;
}

void ExistsTerm::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string ExistsTerm::toString() {
    stringstream ss;
    ss << "(exists (";

    for(vector<shared_ptr<SortedVariable>>::iterator it = bindings.begin(); it != bindings.end(); it++) {
        if(it != bindings.begin())
            ss << " ";
        ss << "(" << (*it)->toString() << ")";
    }

    ss << ") " << term->toString() << ")";

    return ss.str();
}

/* ================================== AnnotatedTerm =================================== */
AnnotatedTerm::AnnotatedTerm(shared_ptr<Term> term,
                             vector<shared_ptr<Attribute>> &attributes)
        : term(term) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

shared_ptr<Term> AnnotatedTerm::getTerm() {
    return term;
}

void AnnotatedTerm::setTerm(shared_ptr<Term> term) {
    this->term = term;
}

vector<shared_ptr<Attribute>> &AnnotatedTerm::getAttributes() {
    return attributes;
}

void AnnotatedTerm::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string AnnotatedTerm::toString() {
    stringstream ss;
    ss << "( ! " << term->toString() << " ";

    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin(); it != attributes.end(); it++) {
        if(it != attributes.begin())
            ss << " ";
        ss << (*it)->toString();
    }

    ss << ")";
    return ss.str();
}