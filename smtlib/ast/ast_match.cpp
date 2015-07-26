#include "ast_match.h"
#include "ast_sort.h"

#include <sstream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

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
    for (auto symbolIt = symbols.begin(); symbolIt != symbols.end(); symbolIt++) {
        ss << " " << (*symbolIt)->toString();
    }
    ss << ")";
    return ss.str();
}

/* ===================================== MatchCase ==================================== */
void MatchCase::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string MatchCase::toString() {
    stringstream ss;
    ss << "(" << pattern->toString() << " " << term->toString() << ")";
    return ss.str();
}