#include "smt_fun.h"

#include <sstream>

using namespace std;
using namespace smt::ast;

/* ================================ FunctionDeclaration =============================== */

FunctionDeclaration::FunctionDeclaration(shared_ptr<Symbol> symbol,
                                         const vector<shared_ptr<SortedVariable>> &params,
                                         shared_ptr<Sort> sort)
        : symbol(symbol), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

shared_ptr<Symbol> FunctionDeclaration::getSymbol() {
    return symbol;
}

void FunctionDeclaration::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

vector<shared_ptr<SortedVariable>> &FunctionDeclaration::getParams() {
    return params;
}

shared_ptr<Sort> FunctionDeclaration::getSort() {
    return sort;
}

void FunctionDeclaration::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

string FunctionDeclaration::toString() {
    stringstream ss;
    ss << symbol << " ( ";

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
                                       shared_ptr<ITerm> body)
        : body(body) {
    signature = make_shared<FunctionDeclaration>(symbol, params, sort);
}

shared_ptr<FunctionDeclaration> FunctionDefinition::getSignature() {
    return signature;
}

void FunctionDefinition::setSignature(shared_ptr<FunctionDeclaration> signature) {
    this->signature = signature;
}

shared_ptr<ITerm> FunctionDefinition::getBody() {
    return body;
}

void FunctionDefinition::setBody(shared_ptr<ITerm> body) {
    this->body = body;
}

string FunctionDefinition::toString() {
    stringstream ss;
    ss << signature->toString() << " " << body->toString();
    return ss.str();
}