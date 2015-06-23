#include "ast_sortedness_checker.h"
#include "ast_syntax_checker.h"
#include "../ast/ast_command.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_theory.h"
#include "../parser/smt_parser.h"
#include "../util/smt_logger.h"


#include <sstream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

shared_ptr<SortednessChecker::SortednessCheckError>
SortednessChecker::addError(string message, AstNode const *node,
                            shared_ptr<SortednessChecker::SortednessCheckError> err) {
    if(!err) {
        shared_ptr<SortednessCheckErrorInfo> errInfo = make_shared<SortednessCheckErrorInfo>();
        errInfo->message = message;

        err = make_shared<SortednessCheckError>();
        err->infos.push_back(errInfo);
        err->node = node;

        errors[string(node->getFilename()->c_str())].push_back(err);
    } else {
        shared_ptr<SortednessCheckErrorInfo> errInfo = make_shared<SortednessCheckErrorInfo>();
        errInfo->message = message;
        err->infos.push_back(errInfo);
    }

    return err;
}

shared_ptr<SortednessChecker::SortednessCheckError>
SortednessChecker::addError(string message, AstNode const *node,
                            shared_ptr<SortInfo> sortInfo,
                            shared_ptr<SortednessChecker::SortednessCheckError> err) {
    if(!err) {
        shared_ptr<SortednessCheckErrorInfo> errInfo = make_shared<SortednessCheckErrorInfo>();
        errInfo->message = message;
        errInfo->sortInfo = sortInfo;

        err = make_shared<SortednessCheckError>();
        err->infos.push_back(errInfo);
        err->node = node;

        errors[string(node->getFilename()->c_str())].push_back(err);
    } else {
        shared_ptr<SortednessCheckErrorInfo> errInfo = make_shared<SortednessCheckErrorInfo>();
        errInfo->message = message;
        errInfo->sortInfo = sortInfo;

        err->infos.push_back(errInfo);
    }

    return err;
}

shared_ptr<SortednessChecker::SortednessCheckError>
SortednessChecker::addError(string message, AstNode const *node,
                            shared_ptr<FunInfo> funInfo,
                            shared_ptr<SortednessChecker::SortednessCheckError> err) {
    if(!err) {
        shared_ptr<SortednessCheckErrorInfo> errInfo = make_shared<SortednessCheckErrorInfo>();
        errInfo->message = message;
        errInfo->funInfo = funInfo;

        err = make_shared<SortednessCheckError>();
        err->infos.push_back(errInfo);
        err->node = node;

        errors[string(node->getFilename()->c_str())].push_back(err);
    } else {
        shared_ptr<SortednessCheckErrorInfo> errInfo = make_shared<SortednessCheckErrorInfo>();
        errInfo->message = message;
        errInfo->funInfo = funInfo;

        err->infos.push_back(errInfo);
    }

    return err;
}

void SortednessChecker::addError(string message, AstNode const *node) {
    shared_ptr<SortednessCheckErrorInfo> errInfo = make_shared<SortednessCheckErrorInfo>();
    errInfo->message = message;

    shared_ptr<SortednessCheckError> err = make_shared<SortednessCheckError>();
    err = make_shared<SortednessCheckError>();
    err->infos.push_back(errInfo);
    err->node = node;

    errors[string(node->getFilename()->c_str())].push_back(err);
}

void SortednessChecker::addError(string message, AstNode const *node,
                                 shared_ptr<SortInfo> sortInfo) {
    shared_ptr<SortednessCheckErrorInfo> errInfo = make_shared<SortednessCheckErrorInfo>();
    errInfo->message = message;
    errInfo->sortInfo = sortInfo;

    shared_ptr<SortednessCheckError> err = make_shared<SortednessCheckError>();
    err = make_shared<SortednessCheckError>();
    err->infos.push_back(errInfo);
    err->node = node;

    errors[string(node->getFilename()->c_str())].push_back(err);
}

void SortednessChecker::addError(string message, AstNode const *node,
                                 shared_ptr<FunInfo> funInfo) {
    shared_ptr<SortednessCheckErrorInfo> errInfo = make_shared<SortednessCheckErrorInfo>();
    errInfo->message = message;
    errInfo->funInfo = funInfo;

    shared_ptr<SortednessCheckError> err = make_shared<SortednessCheckError>();
    err = make_shared<SortednessCheckError>();
    err->infos.push_back(errInfo);
    err->node = node;

    errors[string(node->getFilename()->c_str())].push_back(err);
}

bool SortednessChecker::equalSignatures(const vector<shared_ptr<Sort>> &sig1, const vector<shared_ptr<Sort>> &sig2) {
    if(sig1.size() != sig2.size())
        return false;

    for(unsigned long i = 0; i < sig1.size(); i++) {
        if(sig1[i]->toString() != sig2[i]->toString())
            return false;
    }

    return true;
}

bool SortednessChecker::equalParamSignatures(const vector<shared_ptr<Symbol>> &params1,
                                             const vector<shared_ptr<Sort>> &sig1,
                                             const vector<shared_ptr<Symbol>> &params2,
                                             const vector<shared_ptr<Sort>> &sig2) {
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

bool SortednessChecker::equalParamSorts(const vector<shared_ptr<Symbol>> &params1, const shared_ptr<Sort> sort1,
                                        const vector<shared_ptr<Symbol>> &params2, const shared_ptr<Sort> sort2,
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
            if (mapping.find(str1) != mapping.end()) {
                return mapping[str1] == str2;
            } else {
                mapping[str1] = str2;
                return true;
            }
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

shared_ptr<SortInfo> SortednessChecker::duplicate(SortSymbolDeclaration const *node) {
    shared_ptr<SortInfo> null;
    string name = node->getIdentifier()->toString();
    shared_ptr<SymbolTable> table = arg->getTopLevel();
    unordered_map<string, shared_ptr<SortInfo>> &sorts = table->getSorts();

    if(sorts.find(name) == sorts.end())
        return null;
    else
        return sorts[name];
}

shared_ptr<FunInfo> SortednessChecker::duplicate(SpecConstFunDeclaration const *node) {
    shared_ptr<FunInfo> null;
    string name = node->getConstant()->toString();
    shared_ptr<SymbolTable> table = arg->getTopLevel();
    unordered_map<string, vector<shared_ptr<FunInfo>>> &funs = table->getFuns();

    if(funs.find(name) == funs.end()) {
        return null;
    } else {
        vector<shared_ptr<FunInfo>> decls = funs[name];
        for(vector<shared_ptr<FunInfo>>::iterator it = decls.begin(); it != decls.end(); it++) {
            SpecConstFunDeclaration* casted = dynamic_cast<SpecConstFunDeclaration*>((*it)->declaration.get());
            if(casted && node->getSort()->toString() == casted->getSort()->toString()) {
                return *it;
            }
        }

        return null;
    }
}

shared_ptr<FunInfo> SortednessChecker::duplicate(MetaSpecConstFunDeclaration const *node) {
    shared_ptr<FunInfo> null;
    string name = node->getConstant()->toString();
    shared_ptr<SymbolTable> table = arg->getTopLevel();
    unordered_map<string, vector<shared_ptr<FunInfo>>> &funs = table->getFuns();

    if(funs.find(name) == funs.end()) {
        return null;
    } else {
        vector<shared_ptr<FunInfo>> decls = funs[name];
        for(vector<shared_ptr<FunInfo>>::iterator it = decls.begin(); it != decls.end(); it++) {
            MetaSpecConstFunDeclaration* casted = dynamic_cast<MetaSpecConstFunDeclaration*>((*it)->declaration.get());
            if(casted && node->getSort()->toString() == casted->getSort()->toString()) {
                return *it;
            }
        }

        return null;
    }
}

shared_ptr<FunInfo> SortednessChecker::duplicate(IdentifierFunDeclaration const *node) {
    shared_ptr<FunInfo> null;
    string name = node->getIdentifier()->toString();
    shared_ptr<SymbolTable> table = arg->getTopLevel();
    unordered_map<string, vector<shared_ptr<FunInfo>>> &funs = table->getFuns();

    if(funs.find(name) == funs.end()) {
        return null;
    } else {
        vector<shared_ptr<FunInfo>> decls = funs[name];
        for(vector<shared_ptr<FunInfo>>::iterator it = decls.begin(); it != decls.end(); it++) {
            IdentifierFunDeclaration* casted = dynamic_cast<IdentifierFunDeclaration*>((*it)->declaration.get());
            if(casted && equalSignatures(node->getSignature(), casted->getSignature())) {
                return *it;
            }
        }

        return null;
    }
}

shared_ptr<FunInfo> SortednessChecker::duplicate(ParametricFunDeclaration const *node) {
    shared_ptr<FunInfo> null;
    string name = node->getIdentifier()->toString();
    shared_ptr<SymbolTable> table = arg->getTopLevel();
    unordered_map<string, vector<shared_ptr<FunInfo>>> &funs = table->getFuns();

    if(funs.find(name) == funs.end()) {
        return null;
    } else {
        vector<shared_ptr<FunInfo>> decls = funs[name];
        for(vector<shared_ptr<FunInfo>>::iterator it = decls.begin(); it != decls.end(); it++) {
            ParametricFunDeclaration* casted = dynamic_cast<ParametricFunDeclaration*>((*it)->declaration.get());
            if(casted && equalParamSignatures(node->getParams(), node->getSignature(),
                                              casted->getParams(), casted->getSignature())) {
                return *it;
            }
        }

        return null;
    }
}

void SortednessChecker::loadTheory(string theory) {
    Parser *parser = new Parser;
    shared_ptr<AstNode> ast = parser->parse("input/Theories/" + theory + ".smt2");
    ast->accept(this);
}

void SortednessChecker::loadLogic(string logic) {
    Parser *parser = new Parser;
    shared_ptr<AstNode> ast = parser->parse("input/Logics/" + logic + ".smt2");
    ast->accept(this);
}

void SortednessChecker::visit(AssertCommand const *node) { }

void SortednessChecker::visit(DeclareConstCommand const *node) {
    string name = node->getSymbol()->toString();
    vector<shared_ptr<Sort>> empty;
    shared_ptr<IdentifierFunDeclaration> decl =
            make_shared<IdentifierFunDeclaration>(make_shared<Identifier>(node->getSymbol()), empty);
    shared_ptr<FunInfo> info = duplicate(decl.get());

    if(info) {
        ret = false;
        addError("Constant '" + name + "' already declared", node, info);
    } else {
        shared_ptr<DeclareConstCommand> source =
                shared_ptr<DeclareConstCommand>(const_cast<DeclareConstCommand*>(node));
        arg->getTopLevel()->addFun(name, make_shared<FunInfo>(decl, source));
    }
}

void SortednessChecker::visit(DeclareFunCommand const *node) {
    string name = node->getSymbol()->toString();
    shared_ptr<IdentifierFunDeclaration> decl =
            make_shared<IdentifierFunDeclaration>(make_shared<Identifier>(node->getSymbol()), node->getParams());
    shared_ptr<FunInfo> info = duplicate(decl.get());

    if(info) {
        ret = false;
        addError("Function '" + name + "' already declared with the same signature", node, info);
    } else {
        shared_ptr<DeclareFunCommand> source =
                shared_ptr<DeclareFunCommand>(const_cast<DeclareFunCommand*>(node));
        arg->getTopLevel()->addFun(name, make_shared<FunInfo>(decl, source));
    }
}

void SortednessChecker::visit(DeclareSortCommand const *node) {
    string name = node->getSymbol()->toString();
    shared_ptr<SortSymbolDeclaration> decl = make_shared<SortSymbolDeclaration>(
            make_shared<Identifier>(node->getSymbol()), node->getArity());
    shared_ptr<SortInfo> info = duplicate(decl.get());

    if(info) {
        ret = false;
        addError("Sort symbol '" + name + "' already declared", node, info);
    } else {
        shared_ptr<DeclareSortCommand> source =
                shared_ptr<DeclareSortCommand>(const_cast<DeclareSortCommand*>(node));
        arg->getTopLevel()->addSort(name, make_shared<SortInfo>(decl, source));
    }
}

void SortednessChecker::visit(DefineFunCommand const *node) {
    string name = node->getDefinition()->getSignature()->getSymbol()->toString();

    vector<shared_ptr<Sort>> sig;
    vector<shared_ptr<SortedVariable>> &params = node->getDefinition()->getSignature()->getParams();
    for(vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        sig.push_back((*it)->getSort());
    }

    shared_ptr<IdentifierFunDeclaration> decl =
            make_shared<IdentifierFunDeclaration>(make_shared<Identifier>(
                    node->getDefinition()->getSignature()->getSymbol()), sig);
    shared_ptr<FunInfo> info = duplicate(decl.get());

    if(info) {
        ret = false;
        addError("Function '" + name + "' already declared with the same signature", node, info);
    } else {
        shared_ptr<DefineFunCommand> source =
                shared_ptr<DefineFunCommand>(const_cast<DefineFunCommand*>(node));
        arg->getTopLevel()->addFun(name, make_shared<FunInfo>(decl, node->getDefinition()->getBody(), source));
    }
}

void SortednessChecker::visit(DefineFunRecCommand const *node) {
    string name = node->getDefinition()->getSignature()->getSymbol()->toString();

    vector<shared_ptr<Sort>> sig;
    vector<shared_ptr<SortedVariable>> &params = node->getDefinition()->getSignature()->getParams();
    for(vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        sig.push_back((*it)->getSort());
    }

    shared_ptr<IdentifierFunDeclaration> decl =
            make_shared<IdentifierFunDeclaration>(make_shared<Identifier>(
                    node->getDefinition()->getSignature()->getSymbol()), sig);
    shared_ptr<FunInfo> info = duplicate(decl.get());

    if(info) {
        ret = false;
        addError("Function '" + name + "' already declared with the same signature", node, info);
    } else {
        shared_ptr<DefineFunRecCommand> source =
                shared_ptr<DefineFunRecCommand>(const_cast<DefineFunRecCommand*>(node));
        arg->getTopLevel()->addFun(name, make_shared<FunInfo>(decl, node->getDefinition()->getBody(), source));
    }
}
void SortednessChecker::visit(DefineFunsRecCommand const *node) {
    shared_ptr<DefineFunsRecCommand> source =
            shared_ptr<DefineFunsRecCommand>(const_cast<DefineFunsRecCommand*>(node));

    for(unsigned long i = 0; i < node->getDeclarations().size(); i++) {
        vector<shared_ptr<Sort>> sig;
        shared_ptr<FunctionDeclaration> fundecl = node->getDeclarations()[i];
        string name = fundecl->getSymbol()->toString();
        vector<shared_ptr<SortedVariable>> &params = fundecl->getParams();

        for(vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
            sig.push_back((*it)->getSort());
        }

        shared_ptr<IdentifierFunDeclaration> decl =
                make_shared<IdentifierFunDeclaration>(make_shared<Identifier>(fundecl->getSymbol()), sig);
        shared_ptr<FunInfo> info = duplicate(decl.get());

        if(info) {
            ret = false;
            addError("Function '" + name + "' already declared with the same signature", node, info);
        } else {
            arg->getTopLevel()->addFun(name, make_shared<FunInfo>(decl, node->getBodies()[i], source));
        }
    }
}

void SortednessChecker::visit(DefineSortCommand const *node) {
    string name = node->getSymbol()->toString();
    shared_ptr<SortSymbolDeclaration> decl = make_shared<SortSymbolDeclaration>(
            make_shared<Identifier>(node->getSymbol()),
            make_shared<NumeralLiteral>(node->getParams().size(), 10));
    shared_ptr<SortInfo> info = duplicate(decl.get());

    if(info) {
        ret = false;
        addError("Sort symbol '" + name + "' already declared", node, info);
    } else {
        vector<shared_ptr<Symbol>> params;
        params.insert(params.begin(), node->getParams().begin(), node->getParams().end());
        shared_ptr<DefineSortCommand> source =
                shared_ptr<DefineSortCommand>(const_cast<DefineSortCommand*>(node));
        arg->getTopLevel()->addSort(name, make_shared<SortInfo>(decl, params, node->getSort(), source));
    }
}

void SortednessChecker::visit(GetValueCommand const *node) { }
void SortednessChecker::visit(PopCommand const *node) { }
void SortednessChecker::visit(PushCommand const *node) { }
void SortednessChecker::visit(ResetCommand const *node) { }
void SortednessChecker::visit(SetLogicCommand const *node) {
    loadLogic(node->getLogic()->toString());
}

void SortednessChecker::visit(FunctionDeclaration const *node) { }
void SortednessChecker::visit(FunctionDefinition const *node) { }

void SortednessChecker::visit(Identifier const *node) { }
void SortednessChecker::visit(QualifiedIdentifier const *node) { }

void SortednessChecker::visit(DecimalLiteral const *node) { }
void SortednessChecker::visit(NumeralLiteral const *node) { }
void SortednessChecker::visit(StringLiteral const *node) { }

void SortednessChecker::visit(Logic const *node) {
    vector<shared_ptr<Attribute>> attrs = node->getAttributes();
    for(vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;
        if(attr->getKeyword()->getValue() == ":theories") {
            CompoundAttributeValue* val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            for(vector<shared_ptr<AttributeValue>>::iterator v = val->getValues().begin();
                v != val->getValues().end(); v++) {
                string theory = dynamic_cast<Symbol*>((*v).get())->toString();
                loadTheory(theory);
            }
        }
    }
}

void SortednessChecker::visit(Theory const *node) {
    vector<shared_ptr<Attribute>> attrs = node->getAttributes();
    for(vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;

        if(attr->getKeyword()->getValue() == ":sorts" || attr->getKeyword()->getValue() == ":funs") {
            CompoundAttributeValue* val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            for(vector<shared_ptr<AttributeValue>>::iterator v = val->getValues().begin();
                    v != val->getValues().end(); v++) {
                (*v)->accept(this);
            }
        }
    }
}

void SortednessChecker::visit(Script const *node) {
    const vector<shared_ptr<Command>> &commands = node->getCommands();
    for(vector<shared_ptr<Command>>::const_iterator it = commands.begin(); it != commands.end(); it++) {
        (*it)->accept(this);
    }
}

void SortednessChecker::visit(Sort const *node) { }

void SortednessChecker::visit(CompSExpression const *node) { }

void SortednessChecker::visit(SortSymbolDeclaration const *node) {
    string name = node->getIdentifier()->toString();
    shared_ptr<SortInfo> info = duplicate(node);

   if(info) {
       ret = false;
       addError("Sort symbol '" + name + "' already declared", node, info);
   } else {
       shared_ptr<SortSymbolDeclaration> decl =
               shared_ptr<SortSymbolDeclaration>(const_cast<SortSymbolDeclaration*>(node));
       arg->getTopLevel()->addSort(name, make_shared<SortInfo>(decl, decl));
   }
}

void SortednessChecker::visit(SpecConstFunDeclaration const *node) {
    string name = node->getConstant()->toString();
    shared_ptr<FunInfo> info = duplicate(node);

    if(info) {
        ret = false;
        addError("Specification constant '" + name + "' already declared", node, info);
    } else {
        shared_ptr<SpecConstFunDeclaration> decl =
                shared_ptr<SpecConstFunDeclaration>(const_cast<SpecConstFunDeclaration*>(node));
        arg->getTopLevel()->addFun(name, make_shared<FunInfo>(decl, decl));
    }
}

void SortednessChecker::visit(MetaSpecConstFunDeclaration const *node) {
    string name = node->getConstant()->toString();
    shared_ptr<FunInfo> info = duplicate(node);

    if(info) {
        ret = false;
        addError("Meta specification constant '" + name + "' already declared", node, info);
    } else {
        shared_ptr<MetaSpecConstFunDeclaration> decl =
                shared_ptr<MetaSpecConstFunDeclaration>(const_cast<MetaSpecConstFunDeclaration*>(node));
        arg->getTopLevel()->addFun(name, make_shared<FunInfo>(decl, decl));
    }
}

void SortednessChecker::visit(IdentifierFunDeclaration const *node) {
    string name = node->getIdentifier()->toString();
    shared_ptr<FunInfo> info = duplicate(node);

    if(info) {
        ret = false;
        addError("Function '" + name + "' already declared with the same signature", node, info);
    } else {
        shared_ptr<IdentifierFunDeclaration> decl =
                shared_ptr<IdentifierFunDeclaration>(const_cast<IdentifierFunDeclaration*>(node));
        arg->getTopLevel()->addFun(name, make_shared<FunInfo>(decl, decl));
    }
}

void SortednessChecker::visit(ParametricFunDeclaration const *node) {
    string name = node->getIdentifier()->toString();
    shared_ptr<FunInfo> info = duplicate(node);

    if(info) {
        ret = false;
        addError("Function '" + name + "' already declared with equivalent signature", node, info);
    } else {
        shared_ptr<ParametricFunDeclaration> decl =
                shared_ptr<ParametricFunDeclaration>(const_cast<ParametricFunDeclaration*>(node));
        arg->getTopLevel()->addFun(name, make_shared<FunInfo>(decl, decl));
    }
}

void SortednessChecker::visit(QualifiedTerm const *node) { }
void SortednessChecker::visit(LetTerm const *node) { }
void SortednessChecker::visit(ForallTerm const *node) { }
void SortednessChecker::visit(ExistsTerm const *node) { }
void SortednessChecker::visit(AnnotatedTerm const *node) { }

void SortednessChecker::visit(SortedVariable const *node) { }
void SortednessChecker::visit(VarBinding const *node) { }

string SortednessChecker::getErrors() {
    stringstream ss;

    for(map<string, vector<shared_ptr<SortednessCheckError>>>::iterator it = errors.begin();
        it != errors.end(); it++) {
        string file = it->first;
        vector<shared_ptr<SortednessCheckError>> errs = it->second;

        ss << "In file " << file << endl;

        for(vector<shared_ptr<SortednessCheckError>>::iterator itt = errs.begin(); itt != errs.end(); itt++) {
            shared_ptr<SortednessCheckError> err = *itt;
            ss << "\t" << err->node->getRowLeft() << ":" << err->node->getColLeft()
            << " - " << err->node->getRowRight() << ":" << err->node->getColRight() << "   ";

            string nodestr = err->node->toString();
            if (nodestr.length() > 100)
                ss << string(nodestr, 100);
            else
                ss << nodestr;

            ss <<  endl;

            for (vector<shared_ptr<SortednessCheckErrorInfo>>::iterator info = err->infos.begin();
                 info != err->infos.end(); info++) {
                ss << "\t" << (*info)->message << endl;

                if((*info)->sortInfo) {
                    shared_ptr<AstNode> source = (*info)->sortInfo->source;
                    ss << "Previously, in file " << source->getFilename() << " "
                       << source->getRowLeft() << ":" << source->getColLeft() << " - "
                       << source->getRowRight() << ":" << source->getColRight() << "   ";

                    string sourcestr = source->toString();
                    if (sourcestr.length() > 100)
                        ss << string(sourcestr, 100);
                    else
                        ss << sourcestr;

                } else if((*info)->funInfo) {
                    shared_ptr<AstNode> source = (*info)->sortInfo->source;
                    ss << "Previously, in file " << source->getFilename() << " "
                    << source->getRowLeft() << ":" << source->getColLeft() << " - "
                    << source->getRowRight() << ":" << source->getColRight() << "   ";

                    string sourcestr = source->toString();
                    if (sourcestr.length() > 100)
                        ss << string(sourcestr, 100);
                    else
                        ss << sourcestr;
                }

                ss << endl << endl;
            }
        }
    }

    return ss.str();
}