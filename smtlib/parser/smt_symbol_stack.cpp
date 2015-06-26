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
    if(stack.size() <= 1) {
        return false;
    } else {
        unsigned long size = stack.size();
        stack.erase(stack.begin() + (stack.size() - 1));
        return (stack.size() == size - 1);
    }
}

/*bool SymbolStack::equal(std::shared_ptr<ast::Sort> sort1, std::shared_ptr<ast::Sort> sort2) {
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
    for(unsigned long i = stack.size(); i >=0 ; i--) {
        unordered_map<string, shared_ptr<SortInfo>>::iterator it = stack[i]->getSorts().find(name);
        if(it != stack[i]->getSorts().end())
            result = it->second;
    }
    return result;
}

std::vector<std::shared_ptr<FunInfo>> SymbolStack::getFunInfo(string name) {
    vector<shared_ptr<FunInfo>> result;
    for(unsigned long i = stack.size(); i >=0 ; i--) {
        unordered_map<string, vector<shared_ptr<FunInfo>>>::iterator it = stack[i]->getFuns().find(name);
        if(it != stack[i]->getFuns().end())
            result.insert(result.end(), it->second.begin(), it->second.end());
    }
    return result;
}