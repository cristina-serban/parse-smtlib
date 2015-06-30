#include "smt_symbol_table.h"
#include "../ast/ast_command.h"
#include "../ast/ast_symbol_decl.h"

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

unordered_map<string, shared_ptr<VarInfo>> &SymbolTable::getVars() {
    return vars;
}

shared_ptr<SortInfo> SymbolTable::getSortInfo(string name) {
    unordered_map<string, shared_ptr<SortInfo>>::iterator it = sorts.find(name);
    if (it != sorts.end()) {
        return it->second;
    } else {
        shared_ptr<SortInfo> empty;
        return empty;
    }
}

vector<shared_ptr<FunInfo>> SymbolTable::getFunInfo(string name) {
    unordered_map<string, vector<shared_ptr<FunInfo>>>::iterator it = funs.find(name);
    if (it != funs.end()) {
        return it->second;
    } else {
        vector<shared_ptr<FunInfo>> empty;
        return empty;
    }
}

shared_ptr<VarInfo> SymbolTable::getVarInfo(string name) {
    unordered_map<string, shared_ptr<VarInfo>>::iterator it = vars.find(name);
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
    vector<shared_ptr<SortInfo>> sinfos;
    for(auto it : sorts) {
        sinfos.push_back(it.second);
    }

    for(auto it : sinfos) {
        if(!dynamic_pointer_cast<SortSymbolDeclaration>(it->source)) {
            sorts.erase(it->name);
        }
    }

    // Erase function information that does not come from theory files
    vector<string> fkeys;
    vector<vector<shared_ptr<FunInfo>>> finfos;
    for(auto it : funs) {
        fkeys.push_back(it.first);
        finfos.push_back(it.second);
    }

    for(int i = 0; i < fkeys.size(); i++) {
        vector<shared_ptr<FunInfo>>& info = funs[fkeys[i]];
        for(int j = 0; j < finfos[i].size(); j++) {
            if(!dynamic_pointer_cast<FunSymbolDeclaration>(finfos[i][j]->source)) {
                info.erase(info.begin() + j);
            }
        }
        if(info.empty())
            funs.erase(fkeys[i]);
    }
}