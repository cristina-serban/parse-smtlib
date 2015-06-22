#include "smt_symbol_table.h"
#include "../ast/ast_command.h"

#include <utility>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

bool SymbolTable::equalSignatures(vector<shared_ptr<Sort>> &sig1, vector<shared_ptr<Sort>> &sig2) {
    if(sig1.size() != sig2.size())
        return false;

    for(unsigned long i = 0; i < sig1.size(); i++) {
        if(sig1[i]->toString() != sig2[i]->toString())
            return false;
    }

    return true;
}

bool SymbolTable::equalParamSignatures(vector<shared_ptr<Symbol>> &params1, vector<shared_ptr<Sort>> &sig1,
                                       vector<shared_ptr<Symbol>> &params2, vector<shared_ptr<Sort>> &sig2) {
    if(params1.size() != params2.size() || sig1.size() != sig2.size())
        return false;

    unordered_map<string, string> mapping;
    for(unsigned long i = 0; i < sig1.size(); i++) {
        shared_ptr<Sort> sort1 = sig1[i];
        shared_ptr<Sort> sort2 = sig2[i];

        if(!equalParamSorts(params1, sort1, params2, sort2, mapping))
            return false;
    }

    return mapping.size() == params1.size();
}

bool SymbolTable::equalParamSorts(vector<shared_ptr<Symbol>> &params1, shared_ptr<Sort> sort1,
                                  vector<shared_ptr<Symbol>> &params2, shared_ptr<Sort> sort2,
                                  unordered_map<string, string> &mapping) {

    if(sort1->getParams().size() != sort2->getParams().size())
        return false;

    if(sort1->getParams().size() == 0) {
        bool isParam1 = false;
        bool isParam2 = false;

        string str1 = sort1->toString();
        string str2 = sort2->toString();

        for(unsigned long j = 0; j < params1.size(); j++) {
            if(params1[j]->toString() == str1)
                isParam1 = true;
            if(params2[j]->toString() == str2)
                isParam2 = true;
        }

        if((isParam1 && !isParam2) || (!isParam1 && isParam2)) {
            return false;
        } else if(isParam1) {
            if (mapping.find(str1) != mapping.end())
                return false;
            mapping[str1] = str2;
            return true;
        } else {
            return str1 == str2;
        }
    } else {
        if(sort1->getIdentifier()->toString() != sort2->getIdentifier()->toString())
            return false;

        for(unsigned long k = 0; k < sort1->getParams().size(); k++) {
            if(!equalParamSorts(params1, sort1->getParams()[k], params2, sort2->getParams()[k], mapping))
                return false;
        }

        return true;
    }
}

const unordered_map<string,
        shared_ptr<SortSymbolDeclaration>> &SymbolTable::getSortDeclarations() const {
    return sortDeclarations;
}

unordered_map<string,
        shared_ptr<SortSymbolDeclaration>> &SymbolTable::getSortDeclarations() {
    return sortDeclarations;
}

const unordered_map<string, pair<vector<shared_ptr<Symbol>>,
        shared_ptr<Sort>>> &SymbolTable::getSortDefinitions() const {
    return sortDefinitions;
}

unordered_map<string, pair<vector<shared_ptr<Symbol>>,
        shared_ptr<Sort>>> &SymbolTable::getSortDefinitions() {
    return sortDefinitions;
}

const unordered_map<string,
        vector<shared_ptr<FunSymbolDeclaration>>> &SymbolTable::getFuns() const {
    return funs;
}

unordered_map<string,
        vector<shared_ptr<FunSymbolDeclaration>>> &SymbolTable::getFuns() {
    return funs;
}

const unordered_map<string, shared_ptr<SortedVariable>> &SymbolTable::getVars() const {
    return vars;
}

unordered_map<string, shared_ptr<SortedVariable>> &SymbolTable::getVars() {
    return vars;
}

bool SymbolTable::addSort(shared_ptr<SortSymbolDeclaration> node) {
    string name = node->getIdentifier()->toString();
    if(sortDeclarations.find(name) == sortDeclarations.end()) {
        sortDeclarations[name] = node;
        return true;
    } else {
        return false;
    }
}

bool SymbolTable::addSort(shared_ptr<DeclareSortCommand> node) {
	string name = node->getSymbol()->toString();
    if(sortDeclarations.find(name) == sortDeclarations.end()) {
        sortDeclarations[name] = make_shared<SortSymbolDeclaration>(
                make_shared<Identifier>(node->getSymbol()), node->getArity());
        return true;
    } else {
        return false;
    }
}

bool SymbolTable::addSort(shared_ptr<DefineSortCommand> node) {
    string name = node->getSymbol()->toString();
    if(sortDeclarations.find(name) == sortDeclarations.end()) {
        sortDeclarations[name] = make_shared<SortSymbolDeclaration>(
                make_shared<Identifier>(node->getSymbol()),
                make_shared<NumeralLiteral>(node->getParams().size(), 10));

        vector<shared_ptr<Symbol>> params;
        params.insert(params.begin(), node->getParams().begin(), node->getParams().end());

        pair<vector<shared_ptr<Symbol>>,
                shared_ptr<Sort>> def (params, node->getSort());
        sortDefinitions[name] = def;
        return true;
    } else {
        return false;
    }
}

bool SymbolTable::addFun(shared_ptr<SpecConstFunDeclaration> node) {
    string name = node->getConstant()->toString();
    funs[name].push_back(node);
    return true;
}

bool SymbolTable::addFun(shared_ptr<MetaSpecConstFunDeclaration> node) {
    string name = node->getConstant()->toString();
    funs[name].push_back(node);
    return true;
}

bool SymbolTable::addFun(shared_ptr<IdentifierFunDeclaration> node) {
    string name = node->getIdentifier()->toString();
    if(funs.find(name) == funs.end()) {
        funs[name].push_back(node);
        return true;
    } else {
        vector<shared_ptr<FunSymbolDeclaration>> decls = funs[name];
        for(vector<shared_ptr<FunSymbolDeclaration>>::iterator it = decls.begin(); it != decls.end(); it++) {
            IdentifierFunDeclaration* casted = dynamic_cast<IdentifierFunDeclaration*>((*it).get());
            if(casted && equalSignatures(node->getSignature(), casted->getSignature())) {
                return false;
            }
        }

        funs[name].push_back(node);
        return true;
    }
}

bool SymbolTable::addFun(shared_ptr<ParametricFunDeclaration> node) {
    string name = node->getIdentifier()->toString();
    if(funs.find(name) == funs.end()) {
        funs[name].push_back(node);
        return true;
    } else {
        vector<shared_ptr<FunSymbolDeclaration>> decls = funs[name];
        for(vector<shared_ptr<FunSymbolDeclaration>>::iterator it = decls.begin(); it != decls.end(); it++) {
            ParametricFunDeclaration* casted = dynamic_cast<ParametricFunDeclaration*>((*it).get());
            if(casted && equalParamSignatures(node->getParams(), node->getSignature(),
                                              casted->getParams(), casted->getSignature())) {
                return false;
            }
        }

        funs[name].push_back(node);
        return true;
    }
}

bool SymbolTable::addFun(shared_ptr<DeclareConstCommand> node) {
    vector<shared_ptr<Sort>> empty;
    shared_ptr<IdentifierFunDeclaration> ptr =
            make_shared<IdentifierFunDeclaration>(make_shared<Identifier>(node->getSymbol()), empty);

    return addFun(ptr);
}

bool SymbolTable::addFun(shared_ptr<DeclareFunCommand> node) {
    shared_ptr<IdentifierFunDeclaration> ptr =
            make_shared<IdentifierFunDeclaration>(make_shared<Identifier>(node->getSymbol()), node->getParams());

    return addFun(ptr);
}

bool SymbolTable::addFun(shared_ptr<DefineFunCommand> node) {
    vector<shared_ptr<Sort>> sig;
    vector<shared_ptr<SortedVariable>> &params = node->getDefinition()->getSignature()->getParams();
    for(vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        sig.push_back((*it)->getSort());
    }

    shared_ptr<IdentifierFunDeclaration> ptr =
            make_shared<IdentifierFunDeclaration>(make_shared<Identifier>(
                    node->getDefinition()->getSignature()->getSymbol()), sig);

    return addFun(ptr);
}

bool SymbolTable::addFun(shared_ptr<DefineFunRecCommand> node) {
    vector<shared_ptr<Sort>> sig;
    vector<shared_ptr<SortedVariable>> &params = node->getDefinition()->getSignature()->getParams();
    for(vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        sig.push_back((*it)->getSort());
    }

    shared_ptr<IdentifierFunDeclaration> ptr =
            make_shared<IdentifierFunDeclaration>(make_shared<Identifier>(
                    node->getDefinition()->getSignature()->getSymbol()), sig);

    return addFun(ptr);
}

bool SymbolTable::addFun(shared_ptr<DefineFunsRecCommand> node) {
    bool valid = true;
    for(vector<shared_ptr<FunctionDeclaration>>::iterator itt = node->getDeclarations().begin();
            itt != node->getDeclarations().end(); itt++) {
        vector<shared_ptr<Sort>> sig;
        vector<shared_ptr<SortedVariable>> &params = (*itt)->getParams();

        for(vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
            sig.push_back((*it)->getSort());
        }

        shared_ptr<IdentifierFunDeclaration> ptr =
                make_shared<IdentifierFunDeclaration>(make_shared<Identifier>((*itt)->getSymbol()), sig);

        if(!addFun(ptr))
            valid = false;
    }

    return valid;
}

bool SymbolTable::addVariable(shared_ptr<SortedVariable> node) {
    string name = node->getSymbol()->toString();
    if(vars.find(name) == vars.end()) {
        vars[name] = node;
        return true;
    } else {
        return false;
    }
}
