#include "smt_fun.h"

using namespace std;
using namespace smt;

/* ================================ FunctionDeclaration =============================== */

FunctionDeclaration::FunctionDeclaration(shared_ptr<Symbol> symbol,
                                         vector<shared_ptr<SortedVariable>> &params,
                                         shared_ptr<Sort> type) {
    setSymbol(symbol);
    setType(type);
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

shared_ptr<Sort> FunctionDeclaration::getType() {
    return type;
}

void FunctionDeclaration::setType(shared_ptr<Sort> type) {
    this->type = type;
}

string FunctionDeclaration::toString() {
    return "";
}

/* ================================ FunctionDefinition ================================ */

FunctionDefinition::FunctionDefinition(shared_ptr<FunctionDeclaration> signature,
                                       shared_ptr<ITerm> body) {
    setSignature(signature);
    setBody(body);
}

FunctionDefinition::FunctionDefinition(shared_ptr<Symbol> symbol,
                                       vector<shared_ptr<SortedVariable>> &params,
                                       shared_ptr<Sort> type,
                                       shared_ptr<ITerm> body) {
    signature = make_shared<FunctionDeclaration>(symbol, params, type);
    setBody(body);
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