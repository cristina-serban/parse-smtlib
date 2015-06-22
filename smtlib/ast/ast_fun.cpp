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

const shared_ptr<Symbol> FunctionDeclaration::getSymbol() const {
    return symbol;
}

shared_ptr<Symbol> FunctionDeclaration::getSymbol() {
    return symbol;
}

void FunctionDeclaration::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

const vector<shared_ptr<SortedVariable>> &FunctionDeclaration::getParams() const {
    return params;
}

vector<shared_ptr<SortedVariable>> &FunctionDeclaration::getParams() {
    return params;
}

const shared_ptr<Sort> FunctionDeclaration::getSort() const {
    return sort;
}

shared_ptr<Sort> FunctionDeclaration::getSort() {
    return sort;
}

void FunctionDeclaration::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

void FunctionDeclaration::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string FunctionDeclaration::toString() const {
    stringstream ss;
    ss << symbol->toString() << " (";

    for(vector<shared_ptr<SortedVariable>>::const_iterator it = params.begin(); it != params.end(); it++) {
        if(it != params.begin())
            ss << " ";
        ss << (*it)->toString();
    }

    ss << ") " << sort->toString();

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

const shared_ptr<FunctionDeclaration> FunctionDefinition::getSignature() const {
    return signature;
}

shared_ptr<FunctionDeclaration> FunctionDefinition::getSignature() {
    return signature;
}

void FunctionDefinition::setSignature(shared_ptr<FunctionDeclaration> signature) {
    this->signature = signature;
}

const shared_ptr<Term> FunctionDefinition::getBody() const {
    return body;
}

shared_ptr<Term> FunctionDefinition::getBody() {
    return body;
}

void FunctionDefinition::setBody(shared_ptr<Term> body) {
    this->body = body;
}

void FunctionDefinition::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string FunctionDefinition::toString() const {
    stringstream ss;
    ss << signature->toString() << " " << body->toString();
    return ss.str();
}