#include "smt_symbol_table.h"
#include "../ast/ast_command.h"

#include <utility>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;


const unordered_map<string, shared_ptr<SortInfo>> &SymbolTable::getSorts() const {
    return sorts;
}

unordered_map<string, shared_ptr<SortInfo>> &SymbolTable::getSorts() {
    return sorts;
}

const unordered_map<string, vector<shared_ptr<FunInfo>>> &SymbolTable::getFuns() const {
    return funs;
}

unordered_map<string, vector<shared_ptr<FunInfo>>> &SymbolTable::getFuns() {
    return funs;
}

const unordered_map<string, shared_ptr<SortedVariable>> &SymbolTable::getVars() const {
    return vars;
}

unordered_map<string, shared_ptr<SortedVariable>> &SymbolTable::getVars() {
    return vars;
}

bool SymbolTable::addSort(string name, shared_ptr<SortInfo> info) {
    if(sorts.find(name) == sorts.end()) {
        sorts[name] = info;
        return true;
    } else {
        return false;
    }
}

bool SymbolTable::addFun(string name, shared_ptr<FunInfo> info) {
    funs[name].push_back(info);
    return true;
}

/*
bool SymbolTable::addFun(shared_ptr<DefineFunsRecCommand> node) {
    for(unsigned long i = 0; i < node->getDeclarations().size(); i++) {
        vector<shared_ptr<Sort>> sig;
        shared_ptr<FunctionDeclaration> decl = node->getDeclarations()[i];
        vector<shared_ptr<SortedVariable>> &params = decl->getParams();

        for(vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
            sig.push_back((*it)->getSort());
        }

        shared_ptr<IdentifierFunDeclaration> ptr =
                make_shared<IdentifierFunDeclaration>(make_shared<Identifier>(decl->getSymbol()), sig);

        funs[ptr->getIdentifier()->toString()].push_back(make_shared<FunInfo>(ptr, node->getBodies()[i], node));
    }

    return true;
}*/

bool SymbolTable::addVariable(shared_ptr<SortedVariable> node) {
    string name = node->getSymbol()->toString();
    if(vars.find(name) == vars.end()) {
        vars[name] = node;
        return true;
    } else {
        return false;
    }
}