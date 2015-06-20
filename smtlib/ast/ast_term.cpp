#include <sstream>
#include "ast_term.h"

using namespace std;
using namespace smtlib::ast;

/* ================================== QualifiedTerm =================================== */

QualifiedTerm::QualifiedTerm(shared_ptr<QIdentifier> identifier,
                             const vector<shared_ptr<Term>> &terms)
        : identifier(identifier) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

const shared_ptr<QIdentifier> QualifiedTerm::getIdentifier() const {
    return identifier;
}

shared_ptr<QIdentifier> QualifiedTerm::getIdentifier() {
    return identifier;
}

void QualifiedTerm::setIdentifier(shared_ptr<QIdentifier> identifier) {
    this->identifier = identifier;
}

const vector<shared_ptr<Term>> &QualifiedTerm::getTerms() const {
    return terms;
}

vector<shared_ptr<Term>> &QualifiedTerm::getTerms() {
    return terms;
}

void QualifiedTerm::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string QualifiedTerm::toString() const {
    stringstream ss;
    ss << "( " << identifier->toString() << " ";

    for(vector<shared_ptr<Term>>::const_iterator it = terms.begin(); it != terms.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";
    return ss.str();
}

/* ===================================== LetTerm ====================================== */

LetTerm::LetTerm(const vector<shared_ptr<VarBinding>> &bindings,
                 shared_ptr<Term> term)
        : term(term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

const shared_ptr<Term> LetTerm::getTerm() const {
    return term;
}

shared_ptr<Term> LetTerm::getTerm() {
    return term;
}

void LetTerm::setTerm(shared_ptr<Term> term) {
    this->term = term;
}

const vector<shared_ptr<VarBinding>> &LetTerm::getBindings() const {
    return bindings;
}

vector<shared_ptr<VarBinding>> &LetTerm::getBindings() {
    return bindings;
}

void LetTerm::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string LetTerm::toString() const {
    stringstream ss;
    ss << "( let ( ";

    for(vector<shared_ptr<VarBinding>>::const_iterator it = bindings.begin(); it != bindings.end(); it++) {
        ss << "(" << (*it)->toString() << ") ";
    }

    ss << ") " << term->toString() << " )";

    return ss.str();
}

/* ==================================== ForallTerm ==================================== */
ForallTerm::ForallTerm(const vector<shared_ptr<SortedVariable>> &bindings,
                       shared_ptr<Term> term)
        : term(term)  {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

const shared_ptr<Term> ForallTerm::getTerm() const {
    return term;
}

shared_ptr<Term> ForallTerm::getTerm() {
    return term;
}

void ForallTerm::setTerm(shared_ptr<Term> term) {
    this->term = term;
}

const vector<shared_ptr<SortedVariable>> &ForallTerm::getBindings() const {
    return bindings;
}

vector<shared_ptr<SortedVariable>> & ForallTerm::getBindings() {
    return bindings;
}

void ForallTerm::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string ForallTerm::toString() const {
    stringstream ss;
    ss << "( forall ( ";

    for(vector<shared_ptr<SortedVariable>>::const_iterator it = bindings.begin(); it != bindings.end(); it++) {
        ss << "(" << (*it)->toString() << ") ";
    }

    ss << ") " << term->toString() << " )";

    return ss.str();
}

/* ==================================== ExistsTerm ==================================== */
ExistsTerm::ExistsTerm(const vector<shared_ptr<SortedVariable>> &bindings,
                       shared_ptr<Term> term)
        : term(term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

const shared_ptr<Term> ExistsTerm::getTerm() const {
    return term;
}

shared_ptr<Term> ExistsTerm::getTerm() {
    return term;
}

void ExistsTerm::setTerm(shared_ptr<Term> term) {
    this->term = term;
}

const vector<shared_ptr<SortedVariable>> &ExistsTerm::getBindings() const {
    return bindings;
}

vector<shared_ptr<SortedVariable>> &ExistsTerm::getBindings() {
    return bindings;
}

void ExistsTerm::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string ExistsTerm::toString() const {
    stringstream ss;
    ss << "( exists ( ";

    for(vector<shared_ptr<SortedVariable>>::const_iterator it = bindings.begin(); it != bindings.end(); it++) {
        ss << "(" << (*it)->toString() << ") ";
    }

    ss << ") " << term->toString() << " )";

    return ss.str();
}

/* ================================== AnnotatedTerm =================================== */
AnnotatedTerm::AnnotatedTerm(shared_ptr<Term> term,
                             const vector<shared_ptr<Attribute>> &attrs)
        : term(term) {
    this->attrs.insert(this->attrs.end(), attrs.begin(), attrs.end());
}

const shared_ptr<Term> AnnotatedTerm::getTerm() const {
    return term;
}

shared_ptr<Term> AnnotatedTerm::getTerm() {
    return term;
}

void AnnotatedTerm::setTerm(shared_ptr<Term> term) {
    this->term = term;
}

const vector<shared_ptr<Attribute>> &AnnotatedTerm::getAttributes() const {
    return attrs;
}

vector<shared_ptr<Attribute>> &AnnotatedTerm::getAttributes() {
    return attrs;
}

void AnnotatedTerm::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string AnnotatedTerm::toString() const {
    stringstream ss;
    ss << "( ! " << term->toString() << " ";

    for(vector<shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";
    return ss.str();
}