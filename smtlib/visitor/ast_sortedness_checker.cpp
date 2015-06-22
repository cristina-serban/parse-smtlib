#include "ast_sortedness_checker.h"
#include "../ast/ast_command.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

shared_ptr<SortednessChecker::SortednessCheckError>
SortednessChecker::addError(string message, AstNode const *node,
                            shared_ptr<SortednessChecker::SortednessCheckError> err) {
    if(!err) {
        err = make_shared<SortednessCheckError>();
        err->messages.push_back(message);
        err->node = node;
        errors[currentFile].push_back(err);
    } else {
        err->messages.push_back(message);
    }

    return err;
}

void SortednessChecker::visit(Attribute const *node) { }
void SortednessChecker::visit(CompoundAttributeValue const *node) { }

void SortednessChecker::visit(Symbol const *node) { }
void SortednessChecker::visit(Keyword const *node) { }
void SortednessChecker::visit(MetaSpecConstant const *node) { }
void SortednessChecker::visit(BooleanValue const *node) { }
void SortednessChecker::visit(PropLiteral const *node) { }

void SortednessChecker::visit(AssertCommand const *node) { }
void SortednessChecker::visit(CheckSatCommand const *node) { }
void SortednessChecker::visit(CheckSatAssumCommand const *node) { }
void SortednessChecker::visit(DeclareConstCommand const *node) { }
void SortednessChecker::visit(DeclareFunCommand const *node) { }

void SortednessChecker::visit(DeclareSortCommand const *node) {
    string name = node->getSymbol()->toString();
    shared_ptr<SymbolTable> table = arg->getTopLevel();
    unordered_map<string, shared_ptr<SortSymbolDeclaration>> &decls = table->getSortDeclarations();

    if(decls.find(name) == decls.end()) {
        table->addSort(shared_ptr<DeclareSortCommand>(const_cast<DeclareSortCommand*>(node)));
    } else {
        ret = false;
        shared_ptr<SortednessCheckError> err;
        err = addError("Sort symbol '" + name + "' already declared", node, err);
    }
}

void SortednessChecker::visit(DefineFunCommand const *node) {

}

void SortednessChecker::visit(DefineFunRecCommand const *node) { }
void SortednessChecker::visit(DefineFunsRecCommand const *node) { }

void SortednessChecker::visit(DefineSortCommand const *node) {
    string name = node->getSymbol()->toString();
    shared_ptr<SymbolTable> table = arg->getTopLevel();
    unordered_map<string, shared_ptr<SortSymbolDeclaration>> &decls = table->getSortDeclarations();

    if(decls.find(name) == decls.end()) {
        table->addSort(shared_ptr<DefineSortCommand>(const_cast<DefineSortCommand*>(node)));
    } else {
        ret = false;
        shared_ptr<SortednessCheckError> err;
        err = addError("Sort symbol '" + name + "' already declared", node, err);
    }
}

void SortednessChecker::visit(EchoCommand const *node) { }
void SortednessChecker::visit(ExitCommand const *node) { }
void SortednessChecker::visit(GetAssertsCommand const *node) { }
void SortednessChecker::visit(GetAssignsCommand const *node) { }
void SortednessChecker::visit(GetInfoCommand const *node) { }
void SortednessChecker::visit(GetModelCommand const *node) { }
void SortednessChecker::visit(GetOptionCommand const *node) { }
void SortednessChecker::visit(GetProofCommand const *node) { }
void SortednessChecker::visit(GetUnsatAssumsCommand const *node) { }
void SortednessChecker::visit(GetUnsatCoreCommand const *node) { }
void SortednessChecker::visit(GetValueCommand const *node) { }
void SortednessChecker::visit(PopCommand const *node) { }
void SortednessChecker::visit(PushCommand const *node) { }
void SortednessChecker::visit(ResetCommand const *node) { }
void SortednessChecker::visit(ResetAssertsCommand const *node) { }
void SortednessChecker::visit(SetInfoCommand const *node) { }
void SortednessChecker::visit(SetLogicCommand const *node) { }
void SortednessChecker::visit(SetOptionCommand const *node) { }

void SortednessChecker::visit(FunctionDeclaration const *node) { }
void SortednessChecker::visit(FunctionDefinition const *node) { }

void SortednessChecker::visit(Identifier const *node) { }
void SortednessChecker::visit(QualifiedIdentifier const *node) { }

void SortednessChecker::visit(DecimalLiteral const *node) { }
void SortednessChecker::visit(NumeralLiteral const *node) { }
void SortednessChecker::visit(StringLiteral const *node) { }

void SortednessChecker::visit(Logic const *node) { }
void SortednessChecker::visit(Theory const *node) { }
void SortednessChecker::visit(Script const *node) { }

void SortednessChecker::visit(Sort const *node) { }

void SortednessChecker::visit(CompSExpression const *node) { }

void SortednessChecker::visit(SortSymbolDeclaration const *node) {
    string name = node->getIdentifier()->toString();
    shared_ptr<SymbolTable> table = arg->getTopLevel();
    unordered_map<string, shared_ptr<SortSymbolDeclaration>> &decls = table->getSortDeclarations();

    if(decls.find(name) == decls.end()) {
        table->addSort(shared_ptr<SortSymbolDeclaration>(const_cast<SortSymbolDeclaration*>(node)));
    } else {
        ret = false;
        shared_ptr<SortednessCheckError> err;
        err = addError("Sort symbol '" + name + "' already declared", node, err);
    }
}

void SortednessChecker::visit(SpecConstFunDeclaration const *node) {
    string name = node->getConstant()->toString();
    shared_ptr<SymbolTable> table = arg->getTopLevel();
    unordered_map<string, vector<shared_ptr<FunSymbolDeclaration>>> &funs = table->getFuns();

    if(funs.find(name) == funs.end()) {
        table->addFun(shared_ptr<SpecConstFunDeclaration>(const_cast<SpecConstFunDeclaration*>(node)));
    } else {
        shared_ptr<SortednessCheckError> err;
        vector<shared_ptr<FunSymbolDeclaration>> decls = funs[name];

        for(vector<shared_ptr<FunSymbolDeclaration>>::iterator it = decls.begin(); it != decls.end(); it++) {
            SpecConstFunDeclaration* casted = dynamic_cast<SpecConstFunDeclaration*>((*it).get());
            if(casted && node->getSort()->toString() == casted->getSort()->toString()) {
                ret = false;
                err = addError("Specification constant '" + name + "' already declared", node, err);
            }
        }

        table->addFun(shared_ptr<SpecConstFunDeclaration>(const_cast<SpecConstFunDeclaration*>(node)));
    }
}
void SortednessChecker::visit(MetaSpecConstFunDeclaration const *node) {
    string name = node->getConstant()->toString();
    shared_ptr<SymbolTable> table = arg->getTopLevel();
    unordered_map<string, vector<shared_ptr<FunSymbolDeclaration>>> &funs = table->getFuns();

    if(funs.find(name) == funs.end()) {
        table->addFun(shared_ptr<MetaSpecConstFunDeclaration>(const_cast<MetaSpecConstFunDeclaration*>(node)));
    } else {
        shared_ptr<SortednessCheckError> err;
        vector<shared_ptr<FunSymbolDeclaration>> decls = funs[name];
        for(vector<shared_ptr<FunSymbolDeclaration>>::iterator it = decls.begin(); it != decls.end(); it++) {
            MetaSpecConstFunDeclaration* casted = dynamic_cast<MetaSpecConstFunDeclaration*>((*it).get());
            if(casted && node->getSort()->toString() == casted->getSort()->toString()) {
                ret = false;
                err = addError("Meta specification constant '" + name + "' already declared", node, err);
            }
        }

        table->addFun(shared_ptr<MetaSpecConstFunDeclaration>(const_cast<MetaSpecConstFunDeclaration*>(node)));
    }
}
void SortednessChecker::visit(IdentifierFunDeclaration const *node) { }
void SortednessChecker::visit(ParametricFunDeclaration const *node) { }

void SortednessChecker::visit(QualifiedTerm const *node) { }
void SortednessChecker::visit(LetTerm const *node) { }
void SortednessChecker::visit(ForallTerm const *node) { }
void SortednessChecker::visit(ExistsTerm const *node) { }
void SortednessChecker::visit(AnnotatedTerm const *node) { }

void SortednessChecker::visit(SortedVariable const *node) { }
void SortednessChecker::visit(VarBinding const *node) { }