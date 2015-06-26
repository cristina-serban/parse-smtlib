#include "smt_symbol_stack.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

SymbolStack::SymbolStack() {
    pushLevel();
}

shared_ptr<SymbolTable> SymbolStack::getTopLevel() {
    return stack[stack.size() - 1];
}

vector<shared_ptr<SymbolTable>> &SymbolStack::getStack() {
    return stack;
}

bool SymbolStack::pushLevel() {
    unsigned long size = stack.size();
    stack.push_back(make_shared<SymbolTable>());
    return (stack.size() == size + 1);
}

bool SymbolStack::popLevel() {
    if (stack.size() <= 1) {
        return false;
    } else {
        unsigned long size = stack.size();
        stack.erase(stack.begin() + (stack.size() - 1));
        return (stack.size() == size - 1);
    }
}

/*bool SymbolStack::equal(shared_ptr<Sort> sort1, shared_ptr<Sort> sort2) {
    shared_ptr<SortInfo> info1;
    shared_ptr<SortInfo> info2;

    if(sort1->toString() == sort2->toString()) {
        return true;
    }

    if(sort1->getParams() != sort2->getParams()) {

    } else {

    }

    return false;
}*/

shared_ptr<SortInfo> SymbolStack::getSortInfo(string name) {
    shared_ptr<SortInfo> result;
    for (unsigned long i = stack.size(); i >= 0; i--) {
        unordered_map<string, shared_ptr<SortInfo>>::iterator it = stack[i]->getSorts().find(name);
        if (it != stack[i]->getSorts().end())
            result = it->second;
    }
    return result;
}

vector<shared_ptr<FunInfo>> SymbolStack::getFunInfo(string name) {
    vector<shared_ptr<FunInfo>> result;
    for (unsigned long i = stack.size(); i >= 0; i--) {
        unordered_map<string, vector<shared_ptr<FunInfo>>>::iterator it = stack[i]->getFuns().find(name);
        if (it != stack[i]->getFuns().end())
            result.insert(result.end(), it->second.begin(), it->second.end());
    }
    return result;
}

shared_ptr<SortInfo> SymbolStack::duplicate(shared_ptr<SortInfo> info) {
    shared_ptr<SortInfo> dupInfo;
    return dupInfo;
}

shared_ptr<FunInfo> SymbolStack::duplicate(shared_ptr<FunInfo> info) {
    shared_ptr<FunInfo> dupInfo;
    return dupInfo;
}

shared_ptr<VariableInfo> SymbolStack::duplicate(shared_ptr<VariableInfo> info) {
    shared_ptr<VariableInfo> dupInfo;
    return dupInfo;
}

shared_ptr<Sort> SymbolStack::expand(shared_ptr<Sort> sort) {
    //TODO
    return sort;
}

bool SymbolStack::equal(shared_ptr<Sort> sort1,
                        shared_ptr<Sort> sort2) {
    return expand(sort1)->toString() == expand(sort2)->toString();
}

bool SymbolStack::equal(vector<shared_ptr<Symbol>> &params1,
                        shared_ptr<Sort> sort1,
                        vector<shared_ptr<Symbol>> &params2,
                        shared_ptr<Sort> sort2,
                        unordered_map<string, string> &mapping) {
    sort1 = expand(sort1);
    sort2 = expand(sort2);

    if (sort1->getParams().size() != sort2->getParams().size())
        return false;

    if (sort1->getParams().size() == 0) {
        bool isParam1 = false;
        bool isParam2 = false;

        string str1 = sort1->toString();
        string str2 = sort2->toString();

        for (unsigned long j = 0; j < params1.size(); j++) {
            if (params1[j]->toString() == str1)
                isParam1 = true;
            if (params2[j]->toString() == str2)
                isParam2 = true;
        }

        if ((isParam1 && !isParam2) || (!isParam1 && isParam2)) {
            return false;
        } else if (isParam1) {
            if (mapping.find(str1) != mapping.end()) {
                return mapping[str1] == str2;
            } else {
                mapping[str1] = str2;
                return true;
            }
        } else {
            return equal(sort1, sort2);
        }
    } else {
        if (sort1->getIdentifier()->toString() != sort2->getIdentifier()->toString())
            return false;

        for (unsigned long k = 0; k < sort1->getParams().size(); k++) {
            if (!equal(params1, sort1->getParams()[k], params2, sort2->getParams()[k], mapping))
                return false;
        }

        return true;
    }
}

bool SymbolStack::equal(vector<shared_ptr<Sort>> &signature1,
                        vector<shared_ptr<Sort>> &signature2) {
    if (signature1.size() != signature1.size())
        return false;

    for (unsigned long i = 0; i < signature1.size(); i++) {
        if (!equal(signature1[i], signature2[i]))
            return false;
    }

    return true;
}

bool SymbolStack::equal(vector<shared_ptr<Symbol>> &params1,
                        vector<shared_ptr<Sort>> &signature1,
                        vector<shared_ptr<Symbol>> &params2,
                        vector<shared_ptr<Sort>> &signature2) {
    if (params1.size() != params2.size() || signature1.size() != signature2.size())
        return false;

    unordered_map<string, string> mapping;
    for (unsigned long i = 0; i < signature1.size(); i++) {
        shared_ptr<Sort> sort1 = signature1[i];
        shared_ptr<Sort> sort2 = signature2[i];

        if (!equal(params1, sort1, params2, sort2, mapping))
            return false;
    }

    return mapping.size() == params1.size();
}

bool SymbolStack::add(shared_ptr<SortInfo> info) {
    if (duplicate(info))
        return false;
    else
        return getTopLevel()->add(info);
}

bool SymbolStack::add(shared_ptr<FunInfo> info) {
    if (duplicate(info))
        return false;
    else
        return getTopLevel()->add(info);
}

bool SymbolStack::add(shared_ptr<VariableInfo> info) {
    if (duplicate(info))
        return false;
    else
        return getTopLevel()->add(info);
}