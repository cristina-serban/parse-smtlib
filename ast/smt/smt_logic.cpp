//
// Created by cristinaserban on 16.04.2015.
//

#include "smt_logic.h"

using namespace smt;
using namespace std;

SmtLogic::SmtLogic(vector<shared_ptr<Attribute>>& attributes) {
    for(vector<shared_ptr<Attribute>>::iterator it = attributes.begin();
        it != attributes.end(); it++) {
        this->attributes.push_back(*it);
    }
}

std::vector<shared_ptr<Attribute>>& SmtLogic::getAttributes() {
    return attributes;
}
