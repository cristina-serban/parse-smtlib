#include <sstream>
#include "smt_term.h"

using namespace std;
using namespace smt::ast;

/* ================================== QualifiedTerm =================================== */

QualifiedTerm::QualifiedTerm(shared_ptr<IQualIdentifier> identifier,
                             const vector<shared_ptr<ITerm>> &terms)
        : identifier(identifier) {
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

string QualifiedTerm::toString() {
    stringstream ss;
    ss << "( " << identifier->toString() << " ";

    for(vector<shared_ptr<ITerm>>::iterator it = terms.begin(); it != terms.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";
    return ss.str();
}

/* ===================================== LetTerm ====================================== */

LetTerm::LetTerm(const vector<shared_ptr<VarBinding>> &bindings,
                 shared_ptr<ITerm> term)
        : term(term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
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

string LetTerm::toString() {
    stringstream ss;
    ss << "( let ( ";

    for(vector<shared_ptr<VarBinding>>::iterator it = bindings.begin(); it != bindings.end(); it++) {
        ss << "(" << (*it)->toString() << ") ";
    }

    ss << ") " << term->toString() << " )";

    return ss.str();
}

/* ==================================== ForallTerm ==================================== */
ForallTerm::ForallTerm(const vector<shared_ptr<SortedVariable>> &bindings,
                       shared_ptr<ITerm> term)
        : term(term)  {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
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

string ForallTerm::toString() {
    stringstream ss;
    ss << "( forall ( ";

    for(vector<shared_ptr<SortedVariable>>::iterator it = bindings.begin(); it != bindings.end(); it++) {
        ss << "(" << (*it)->toString() << ") ";
    }

    ss << ") " << term->toString() << " )";

    return ss.str();
}

/* ==================================== ExistsTerm ==================================== */
ExistsTerm::ExistsTerm(const vector<shared_ptr<SortedVariable>> &bindings,
                       shared_ptr<ITerm> term)
        : term(term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
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

string ExistsTerm::toString() {
    stringstream ss;
    ss << "( exists ( ";

    for(vector<shared_ptr<SortedVariable>>::iterator it = bindings.begin(); it != bindings.end(); it++) {
        ss << "(" << (*it)->toString() << ") ";
    }

    ss << ") " << term->toString() << " )";

    return ss.str();
}

/* ================================== AnnotatedTerm =================================== */
AnnotatedTerm::AnnotatedTerm(shared_ptr<ITerm> term,
                             const vector<shared_ptr<Attribute>> &attrs)
        : term(term) {
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

string AnnotatedTerm::toString() {
    stringstream ss;
    ss << "( ! " << term->toString() << " ";

    for(vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ")";
    return ss.str();
}