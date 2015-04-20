//
// Created by cristinaserban on 17.04.2015.
//

#include "smt_sort.h"

using namespace std;
using namespace smt;

Sort::Sort(std::shared_ptr<IIdentifier> identifier) {
    setIdentifier(identifier);
}

Sort::Sort(shared_ptr<IIdentifier> identifier, vector<std::shared_ptr<Sort>> &params) {
    setIdentifier(identifier);
    for(vector<std::shared_ptr<Sort>>::iterator it = params.begin(); it != params.end(); it++) {
        this->params.push_back(*it);
    }
}

shared_ptr<IIdentifier> Sort::getIdentifier() {
    return identifier;
}

void Sort::setIdentifier(std::shared_ptr<IIdentifier> identifier) {
    this->identifier = identifier;
}

std::vector<std::shared_ptr<Sort>>& Sort::getParams() {
    return params;
}