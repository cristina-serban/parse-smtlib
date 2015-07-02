#include "ast_datatype.h"

#include <sstream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

/* ================================= SortDeclaration ================================== */
SortDeclaration::SortDeclaration(shared_ptr<Symbol> symbol,
                                 shared_ptr<NumeralLiteral> numeral) : symbol(symbol), numeral(numeral) { }

void SortDeclaration::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SortDeclaration::toString() {
    stringstream ss;
    ss << "(" << symbol->toString() << " " << numeral->toString() << ")";
    return ss.str();
}

/* =============================== SelectorDeclaration ================================ */

SelectorDeclaration::SelectorDeclaration(shared_ptr<Symbol> symbol,
                                         shared_ptr<Sort> sort) : symbol(symbol), sort(sort) { }

void SelectorDeclaration::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SelectorDeclaration::toString() {
    stringstream ss;
    ss << "(" << symbol->toString() << " " << sort->toString() << ")";
    return ss.str();
}

/* =============================== ConstructorDeclaration ============================== */

ConstructorDeclaration::ConstructorDeclaration(shared_ptr<Symbol> symbol,
                                               vector<shared_ptr<SelectorDeclaration>>& selectors) : symbol(symbol) {
    this->selectors.insert(this->selectors.begin(), selectors.begin(), selectors.end());
}

void ConstructorDeclaration::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ConstructorDeclaration::toString() {
    stringstream ss;
    ss << "(" << symbol->toString();
    for(auto it : selectors) {
        ss << " " << it->toString();
    }
    ss << ")";
    return ss.str();
}

/* ================================ DatatypeDeclaration =============================== */

SimpleDatatypeDeclaration::SimpleDatatypeDeclaration(vector<shared_ptr<ConstructorDeclaration>>& constructors) {
    this->constructors.insert(this->constructors.begin(), constructors.begin(), constructors.end());
}

void SimpleDatatypeDeclaration::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string SimpleDatatypeDeclaration::toString() {
    stringstream ss;
    ss << "(";
    bool first = true;
    for(auto it : constructors) {
        if(first)
            first = false;
        else
            ss << " ";
        ss << it->toString();
    }
    ss << ")";
    return ss.str();
}

/* =========================== ParametricDatatypeDeclaration ========================== */

ParametricDatatypeDeclaration::ParametricDatatypeDeclaration(vector<shared_ptr<Symbol>> params,
                                                             vector<shared_ptr<ConstructorDeclaration>>& constructors) {
    this->params.insert(this->params.begin(), params.begin(), params.end());
    this->constructors.insert(this->constructors.begin(), constructors.begin(), constructors.end());
}

void ParametricDatatypeDeclaration::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string ParametricDatatypeDeclaration::toString() {
    stringstream ss;
    ss << "( par (";

    bool first = true;
    for(auto it : params) {
        if(first)
            first = false;
        else
            ss << " ";
        ss << it->toString();
    }

    ss << ") (";

    first = true;
    for(auto it : constructors) {
        if(first)
            first = false;
        else
            ss << " ";
        ss << it->toString();
    }

    return ss.str();
}
