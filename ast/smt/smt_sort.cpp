#include "smt_sort.h"

using namespace std;
using namespace smt;

Sort::Sort(shared_ptr<IIdentifier> identifier) {
    setIdentifier(identifier);
}

Sort::Sort(shared_ptr<IIdentifier> identifier, vector<shared_ptr<Sort>> &params) {
    setIdentifier(identifier);
    for(vector<shared_ptr<Sort>>::iterator it = params.begin(); it != params.end(); it++) {
        this->params.push_back(*it);
    }
}

shared_ptr<IIdentifier> Sort::getIdentifier() {
    return identifier;
}

void Sort::setIdentifier(shared_ptr<IIdentifier> identifier) {
    this->identifier = identifier;
}

vector<shared_ptr<Sort>>& Sort::getParams() {
    return params;
}

bool Sort::isParametric() {
    return params.size() != 0;
}