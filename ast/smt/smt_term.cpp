#include "smt_term.h"

using namespace std;
using namespace smt;

/* ================================== QualifiedTerm =================================== */

QualifiedTerm::QualifiedTerm(std::shared_ptr<IQualIdentifier> identifier,
                             std::vector<std::shared_ptr<ITerm>> &terms) {
    setIdentifier(identifier);
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

std::shared_ptr<IQualIdentifier> QualifiedTerm::getIdentifier() {
    return identifier;
}

void QualifiedTerm::setIdentifier(std::shared_ptr<IQualIdentifier> identifier) {
    this->identifier = identifier;
}

std::vector<std::shared_ptr<ITerm>> &QualifiedTerm::getTerms() {
    return terms;
}

/* ===================================== LetTerm ====================================== */

LetTerm::LetTerm(std::vector<std::shared_ptr<VarBinding>> &bindings,
                 std::shared_ptr<ITerm> term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
    setTerm(term);
}

std::shared_ptr<ITerm> LetTerm::getTerm() {
    return term;
}

void LetTerm::setTerm(std::shared_ptr<ITerm> term) {
    this->term = term;
}

std::vector<std::shared_ptr<VarBinding>> &LetTerm::getBindings() {
    return bindings;
}

/* ==================================== ForallTerm ==================================== */
ForallTerm::ForallTerm(std::vector<std::shared_ptr<SortedVariable>> &bindings,
                       std::shared_ptr<ITerm> term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
    setTerm(term);
}

std::shared_ptr<ITerm> ForallTerm::getTerm() {
    return term;
}

void ForallTerm::setTerm(std::shared_ptr<ITerm> term) {
    this->term = term;
}

std::vector<std::shared_ptr<SortedVariable>> &ForallTerm::getBindings() {
    return bindings;
}

/* ==================================== ExistsTerm ==================================== */
ExistsTerm::ExistsTerm(std::vector<std::shared_ptr<SortedVariable>> &bindings,
                       std::shared_ptr<ITerm> term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
    setTerm(term);
}

std::shared_ptr<ITerm> ExistsTerm::getTerm() {
    return term;
}

void ExistsTerm::setTerm(std::shared_ptr<ITerm> term) {
    this->term = term;
}

std::vector<std::shared_ptr<SortedVariable>> &ExistsTerm::getBindings() {
    return bindings;
}

/* ================================== AnnotatedTerm =================================== */
AnnotatedTerm::AnnotatedTerm(std::shared_ptr<ITerm> term,
                             std::vector<std::shared_ptr<Attribute>> &attrs) {
    setTerm(term);
    this->attrs.insert(this->attrs.end(), attrs.begin(), attrs.end());
}

std::shared_ptr<ITerm> AnnotatedTerm::getTerm() {
    return term;
}

void AnnotatedTerm::setTerm(std::shared_ptr<ITerm> term) {
    this->term = term;
}

std::vector<std::shared_ptr<Attribute>> &AnnotatedTerm::getAttrs() {
    return attrs;
}