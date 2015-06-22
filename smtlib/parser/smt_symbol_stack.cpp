#include "smt_symbol_stack.h"

using namespace std;
using namespace smtlib;

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

const std::shared_ptr<SymbolTable> SymbolStack::getTopLevel() const {
    return stack[stack.size() - 1];
}

std::shared_ptr<SymbolTable> SymbolStack::getTopLevel() {
    return stack[stack.size() - 1];
}

const std::vector<std::shared_ptr<SymbolTable>> &SymbolStack::getStack() const {
    return stack;
}

std::vector<std::shared_ptr<SymbolTable>> &SymbolStack::getStack() {
    return stack;
}