#include "ast_match.h"
#include "ast_sort.h"

#include <sstream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

QualifiedConstructor::QualifiedConstructor(shared_ptr<Symbol> symbol,
                                           shared_ptr<Sort> sort) : symbol(symbol), sort(sort) { }

void QualifiedConstructor::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedConstructor::toString() {
    stringstream ss;
    ss << "(as " << symbol->toString() << " " << sort->toString() << ")";
    return ss.str();
}

/* ================================= QualifiedPattern ================================= */

QualifiedPattern::QualifiedPattern(shared_ptr<Constructor> constructor,
                                   vector<shared_ptr<Symbol>>& symbols) : constructor(constructor) {
    this->symbols.insert(this->symbols.begin(), symbols.begin(), symbols.end());
}

void QualifiedPattern::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedPattern::toString() {
    stringstream ss;
    ss << "(" << constructor->toString();
    for(auto it : symbols) {
        ss << " " << it->toString();
    }
    ss << ")";
    return ss.str();
}

/* ===================================== MatchCase ==================================== */
MatchCase::MatchCase(shared_ptr<Pattern> pattern,
                     shared_ptr<Term> term) : pattern(pattern), term(term) {}

void MatchCase::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string MatchCase::toString() {
    stringstream ss;
    ss << "(" << pattern->toString() << " " << term->toString() << ")";
    return ss.str();
}