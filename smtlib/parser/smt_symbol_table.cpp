#include "smt_symbol_table.h"
#include "../ast/ast_command.h"
#include "../ast/ast_symbol_decl.h"

#include <utility>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;


unordered_map<string, shared_ptr<SortInfo>>& SymbolTable::getSorts() {
    return sorts;
}

unordered_map<string, vector<shared_ptr<FunInfo>>>& SymbolTable::getFuns() {
    return funs;
}

unordered_map<string, shared_ptr<VarInfo>>& SymbolTable::getVars() {
    return vars;
}

shared_ptr<SortInfo> SymbolTable::getSortInfo(string name) {
    auto it = sorts.find(name);
    if (it != sorts.end()) {
        return it->second;
    } else {
        shared_ptr<SortInfo> empty;
        return empty;
    }
}

vector<shared_ptr<FunInfo>> SymbolTable::getFunInfo(string name) {
    auto it = funs.find(name);
    if (it != funs.end()) {
        return it->second;
    } else {
        vector<shared_ptr<FunInfo>> empty;
        return empty;
    }
}

shared_ptr<VarInfo> SymbolTable::getVarInfo(string name) {
    auto it = vars.find(name);
    if (it != vars.end()) {
        return it->second;
    } else {
        shared_ptr<VarInfo> empty;
        return empty;
    }
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

bool SymbolTable::add(shared_ptr<VarInfo> info) {
    if(vars.find(info->name) == vars.end()) {
        vars[info->name] = info;
        return true;
    } else {
        return false;
    }
}

void SymbolTable::reset() {
    // Clear all variables
    vars.clear();

    // Erase sort information that does not come from theory files
    vector<shared_ptr<SortInfo>> sortInfos;
    for (auto sortIt = sorts.begin(); sortIt != sorts.end(); sortIt++) {
        sortInfos.push_back(sortIt->second);
    }

    for (auto sortInfoIt = sortInfos.begin(); sortInfoIt != sortInfos.end(); sortInfoIt++) {
        if(!dynamic_pointer_cast<SortSymbolDeclaration>((*sortInfoIt)->source)) {
            sorts.erase((*sortInfoIt)->name);
        }
    }

    // Erase function information that does not come from theory files
    vector<string> funKeys;
    vector<vector<shared_ptr<FunInfo>>> funInfos;
    for (auto funIt = funs.begin(); funIt != funs.end(); funIt++) {
        funKeys.push_back(funIt->first);
        funInfos.push_back(funIt->second);
    }

    for (int i = 0; i < funKeys.size(); i++) {
        vector<shared_ptr<FunInfo>>& info = funs[funKeys[i]];
        for (int j = 0; j < funInfos[i].size(); j++) {
            if(!dynamic_pointer_cast<FunSymbolDeclaration>(funInfos[i][j]->source)) {
                info.erase(info.begin() + j);
            }
        }
        if(info.empty())
            funs.erase(funKeys[i]);
    }
}