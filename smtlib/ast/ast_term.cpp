#include "ast_term.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================== QualifiedTerm =================================== */

QualifiedTerm::QualifiedTerm(shared_ptr<Identifier> identifier,
                             vector<shared_ptr<Term>>& terms)
        : identifier(identifier) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

void QualifiedTerm::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string QualifiedTerm::toString() {
    stringstream ss;
    ss << "(" << identifier->toString() << " ";

    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        if(termIt != terms.begin())
            ss << " ";
        ss << (*termIt)->toString();
    }

    ss << ")";
    return ss.str();
}

/* ===================================== LetTerm ====================================== */

LetTerm::LetTerm(vector<shared_ptr<VarBinding>>& bindings,
                 shared_ptr<Term> term)
        : term(term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

void LetTerm::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string LetTerm::toString() {
    stringstream ss;
    ss << "(let (";

    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        if(bindingIt != bindings.begin())
            ss << " ";
        ss << "(" << (*bindingIt)->toString() << ")";
    }

    ss << ") " << term->toString() << ")";

    return ss.str();
}

/* ==================================== ForallTerm ==================================== */
ForallTerm::ForallTerm(vector<shared_ptr<SortedVariable>>& bindings,
                       shared_ptr<Term> term)
        : term(term)  {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

void ForallTerm::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string ForallTerm::toString() {
    stringstream ss;
    ss << "(forall (";

    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        if(bindingIt != bindings.begin())
            ss << " ";
        ss << "(" << (*bindingIt)->toString() << ")";
    }

    ss << ") " << term->toString() << ")";

    return ss.str();
}

/* ==================================== ExistsTerm ==================================== */
ExistsTerm::ExistsTerm(vector<shared_ptr<SortedVariable>>& bindings,
                       shared_ptr<Term> term)
        : term(term) {
    this->bindings.insert(this->bindings.end(), bindings.begin(), bindings.end());
}

void ExistsTerm::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string ExistsTerm::toString() {
    stringstream ss;
    ss << "(exists (";

    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        if(bindingIt != bindings.begin())
            ss << " ";
        ss << "(" << (*bindingIt)->toString() << ")";
    }

    ss << ") " << term->toString() << ")";

    return ss.str();
}

/* ==================================== MatchTerm ===================================== */
MatchTerm::MatchTerm(std::shared_ptr<Term> term,
                     std::vector<std::shared_ptr<MatchCase>>& cases) : term(term) {
    this->cases.insert(this->cases.begin(), cases.begin(), cases.end());
}

void MatchTerm::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

std::string MatchTerm::toString() {
    stringstream ss;
    ss << "(match " << term->toString();
    for (auto caseIt = cases.begin(); caseIt != cases.end(); caseIt++) {
        ss << " " << (*caseIt)->toString();
    }
    ss << ")";
    return ss.str();
}

/* ================================== AnnotatedTerm =================================== */
AnnotatedTerm::AnnotatedTerm(shared_ptr<Term> term,
                             vector<shared_ptr<Attribute>>& attributes)
        : term(term) {
    this->attributes.insert(this->attributes.end(), attributes.begin(), attributes.end());
}

void AnnotatedTerm::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string AnnotatedTerm::toString() {
    stringstream ss;
    ss << "( ! " << term->toString() << " ";

    for (auto attrIt = attributes.begin(); attrIt != attributes.end(); attrIt++) {
        if(attrIt != attributes.begin())
            ss << " ";
        ss << (*attrIt)->toString();
    }

    ss << ")";
    return ss.str();
}