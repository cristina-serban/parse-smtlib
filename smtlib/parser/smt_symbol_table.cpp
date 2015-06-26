#include "smt_symbol_table.h"
#include "../ast/ast_command.h"

#include <utility>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;


unordered_map<string, shared_ptr<SortInfo>> &SymbolTable::getSorts() {
    return sorts;
}

unordered_map<string, vector<shared_ptr<FunInfo>>> &SymbolTable::getFuns() {
    return funs;
}

unordered_map<string, shared_ptr<VariableInfo>> &SymbolTable::getVars() {
    return vars;
}

shared_ptr<SortInfo> SymbolTable::duplicate (shared_ptr<SortInfo> info) {
    std::shared_ptr<SortInfo> dupInfo;
    return dupInfo;
}

shared_ptr<FunInfo> SymbolTable::duplicate (shared_ptr<FunInfo> info) {
    std::shared_ptr<FunInfo> dupInfo;
    return dupInfo;
}

shared_ptr<VariableInfo> SymbolTable::duplicate (shared_ptr<VariableInfo> info) {
    std::shared_ptr<VariableInfo> dupInfo;
    return dupInfo;
}

bool SymbolTable::add(shared_ptr<SortInfo> info) {
    if(sorts.find(info->name) == sorts.end()) {
        sorts[info->name] = info;
        return true;
    } else {
        return false;
    }
}

bool SymbolTable::add(shared_ptr<FunInfo> info) {
    funs[info->name].push_back(info);
    return true;
}

bool SymbolTable::add(shared_ptr<VariableInfo> info) {
    if(vars.find(info->name) == vars.end()) {
        vars[info->name] = info;
        return true;
    } else {
        return false;
    }
}