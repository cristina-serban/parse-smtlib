#include "smt_sort.h"

using namespace std;
using namespace smt::ast;

Sort::Sort(shared_ptr<Identifier> identifier,
           const vector<shared_ptr<Sort>> &params)
        : identifier(identifier) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

shared_ptr<Identifier> Sort::getIdentifier() {
    return identifier;
}

void Sort::setIdentifier(shared_ptr<Identifier> identifier) {
    this->identifier = identifier;
}

vector<shared_ptr<Sort>>& Sort::getParams() {
    return params;
}

bool Sort::isParametric() {
    return !params.empty();
}