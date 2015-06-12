#include "ast_fun.h"

#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================ FunctionDeclaration =============================== */

FunctionDeclaration::FunctionDeclaration(shared_ptr<Symbol> symbol,
                                         const vector<shared_ptr<SortedVariable>> &params,
                                         shared_ptr<Sort> sort)
        : symbol(symbol), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

shared_ptr<Symbol> FunctionDeclaration::getSymbol() const {
    return symbol;
}

void FunctionDeclaration::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

vector<shared_ptr<SortedVariable>> &FunctionDeclaration::getParams() {
    return params;
}

shared_ptr<Sort> FunctionDeclaration::getSort() const {
    return sort;
}

void FunctionDeclaration::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

void FunctionDeclaration::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string FunctionDeclaration::toString() {
    stringstream ss;
    ss << symbol->toString() << " ( ";

    for(vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << " ) " << sort->toString();

    return ss.str();
}

/* ================================ FunctionDefinition ================================ */

FunctionDefinition::FunctionDefinition(shared_ptr<Symbol> symbol,
                                       const vector<shared_ptr<SortedVariable>> &params,
                                       shared_ptr<Sort> sort,
                                       shared_ptr<Term> body)
        : body(body) {
    signature = make_shared<FunctionDeclaration>(symbol, params, sort);
}

shared_ptr<FunctionDeclaration> FunctionDefinition::getSignature() const {
    return signature;
}

void FunctionDefinition::setSignature(shared_ptr<FunctionDeclaration> signature) {
    this->signature = signature;
}

shared_ptr<Term> FunctionDefinition::getBody() const {
    return body;
}

void FunctionDefinition::setBody(shared_ptr<Term> body) {
    this->body = body;
}

void FunctionDefinition::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string FunctionDefinition::toString() {
    stringstream ss;
    ss << signature->toString() << " " << body->toString();
    return ss.str();
}