#include "ast_var_replacer.h"
#include "../ast/ast_var.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

unordered_map<std::string, std::string> &VariableReplacerContext::getRenamingMap() {
    return renamingMap;
};

void VariableReplacer::visit(shared_ptr<SimpleIdentifier> node) {
    string &name = node->getSymbol()->getValue();

    unordered_map<string, string> &renamingMap = ctx->getRenamingMap();
    unordered_map<string, string>::iterator it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->getSymbol()->setValue(renamingMap[name]);
    }
}

void VariableReplacer::visit(shared_ptr<SortedVariable> node) {
    string &name = node->getSymbol()->getValue();

    unordered_map<string, string> &renamingMap = ctx->getRenamingMap();
    unordered_map<string, string>::iterator it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->getSymbol()->setValue(renamingMap[name]);
    }
}

void VariableReplacer::visit(shared_ptr<VarBinding> node) {
    string &name = node->getSymbol()->getValue();

    unordered_map<string, string> &renamingMap = ctx->getRenamingMap();
    unordered_map<string, string>::iterator it = renamingMap.find(name);

    if (it != renamingMap.end()) {
        node->getSymbol()->setValue(renamingMap[name]);
    }
}