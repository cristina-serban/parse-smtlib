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

bool SymbolTable::addSort(shared_ptr<SortInfo> info) {
    if(sorts.find(info->name) == sorts.end()) {
        sorts[info->name] = info;
        return true;
    } else {
        return false;
    }
}

bool SymbolTable::addFun(shared_ptr<FunInfo> info) {
    funs[info->name].push_back(info);
    return true;
}

bool SymbolTable::addVariable(shared_ptr<VariableInfo> info) {
    if(vars.find(info->name) == vars.end()) {
        vars[info->name] = info;
        return true;
    } else {
        return false;
    }
}