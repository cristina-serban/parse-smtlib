#include "smt_term.h"

using namespace std;
using namespace smt::ast;

/* ================================== QualifiedTerm =================================== */

QualifiedTerm::QualifiedTerm(shared_ptr<IQualIdentifier> identifier,
                             const vector<shared_ptr<ITerm>> &terms) {
    setIdentifier(identifier);
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

shared_ptr<IQualIdentifier> QualifiedTerm::getIdentifier() {
    return identifier;
}

void QualifiedTerm::setIdentifier(shared_ptr<IQualIdentifier> identifier) {
    this->identifier = identifier;
}

vector<shared_ptr<ITerm>> &QualifiedTerm::getTerms() {
    return terms;
}

/* ===================================== LetTerm ====================================== */

LetTerm::LetTerm(const vector<shared_ptr<VarBinding>> &bindings,
                 shared_ptr<ITerm> term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
    setTerm(term);
}

shared_ptr<ITerm> LetTerm::getTerm() {
    return term;
}

void LetTerm::setTerm(shared_ptr<ITerm> term) {
    this->term = term;
}

vector<shared_ptr<VarBinding>> &LetTerm::getBindings() {
    return bindings;
}

/* ==================================== ForallTerm ==================================== */
ForallTerm::ForallTerm(const vector<shared_ptr<SortedVariable>> &bindings,
                       shared_ptr<ITerm> term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
    setTerm(term);
}

shared_ptr<ITerm> ForallTerm::getTerm() {
    return term;
}

void ForallTerm::setTerm(shared_ptr<ITerm> term) {
    this->term = term;
}

vector<shared_ptr<SortedVariable>> &ForallTerm::getBindings() {
    return bindings;
}

/* ==================================== ExistsTerm ==================================== */
ExistsTerm::ExistsTerm(const vector<shared_ptr<SortedVariable>> &bindings,
                       shared_ptr<ITerm> term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
    setTerm(term);
}

shared_ptr<ITerm> ExistsTerm::getTerm() {
    return term;
}

void ExistsTerm::setTerm(shared_ptr<ITerm> term) {
    this->term = term;
}

vector<shared_ptr<SortedVariable>> &ExistsTerm::getBindings() {
    return bindings;
}

/* ================================== AnnotatedTerm =================================== */
AnnotatedTerm::AnnotatedTerm(shared_ptr<ITerm> term,
                             const vector<shared_ptr<Attribute>> &attrs) {
    setTerm(term);
    this->attrs.insert(this->attrs.end(), attrs.begin(), attrs.end());
}

shared_ptr<ITerm> AnnotatedTerm::getTerm() {
    return term;
}

void AnnotatedTerm::setTerm(shared_ptr<ITerm> term) {
    this->term = term;
}

vector<shared_ptr<Attribute>> &AnnotatedTerm::getAttrs() {
    return attrs;
}