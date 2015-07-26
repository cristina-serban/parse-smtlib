#include "ast_identifier.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ==================================== SimpleIdentifier ==================================== */

SimpleIdentifier::SimpleIdentifier(shared_ptr<Symbol> symbol,
                                   vector<shared_ptr<Index>>& indices)
        : symbol(symbol) {
    this->indices.insert(this->indices.end(), indices.begin(), indices.end());
}

bool SimpleIdentifier::isIndexed() {
    return !indices.empty();
}

void SimpleIdentifier::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SimpleIdentifier::toString() {
    if (!isIndexed())
        return symbol->toString();
    else {
        stringstream ss;
        ss << "( _ " << symbol->toString() << " ";
        for (auto indexIt = indices.begin(); indexIt != indices.end(); indexIt++) {
            if (indexIt != indices.begin())
                ss << " ";
            ss << (*indexIt)->toString();
        }
        ss << ")";
        return ss.str();
    }
}

/* =============================== QualifiedIdentifier ================================ */
void QualifiedIdentifier::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string QualifiedIdentifier::toString() {
    stringstream ss;
    ss << "(as " << identifier->toString() << " " << sort->toString() << ")";
    return ss.str();
}