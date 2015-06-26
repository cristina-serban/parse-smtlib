#include "ast_sortedness_checker.h"
#include "ast_syntax_checker.h"
#include "../ast/ast_command.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_theory.h"
#include "../parser/smt_parser.h"
#include "../util/smt_logger.h"


#include <sstream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

shared_ptr<SortednessChecker::SortednessCheckError>
SortednessChecker::addError(string message, shared_ptr<AstNode> node,
                            shared_ptr<SortednessChecker::SortednessCheckError> err) {
    if (!err) {
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
SortednessChecker::addError(string message, shared_ptr<AstNode> node,
                            shared_ptr<SortInfo> sortInfo,
                            shared_ptr<SortednessChecker::SortednessCheckError> err) {
    if (!err) {
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
SortednessChecker::addError(string message, shared_ptr<AstNode> node,
                            shared_ptr<FunInfo> funInfo,
                            shared_ptr<SortednessChecker::SortednessCheckError> err) {
    if (!err) {
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

void SortednessChecker::addError(string message, shared_ptr<AstNode> node) {
    shared_ptr<SortednessCheckErrorInfo> errInfo = make_shared<SortednessCheckErrorInfo>();
    errInfo->message = message;

    shared_ptr<SortednessCheckError> err = make_shared<SortednessCheckError>();
    err = make_shared<SortednessCheckError>();
    err->infos.push_back(errInfo);
    err->node = node;

    errors[string(node->getFilename()->c_str())].push_back(err);
}

void SortednessChecker::addError(string message, shared_ptr<AstNode> node,
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

void SortednessChecker::addError(string message, shared_ptr<AstNode> node,
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

shared_ptr<FunInfo> getInfo(shared_ptr<DeclareConstCommand> node) {
    vector<shared_ptr<Sort>> sig;
    sig.push_back(node->getSort());

    return make_shared<FunInfo>(node->getSymbol()->toString(), sig, node);
}

shared_ptr<FunInfo> getInfo(shared_ptr<DeclareFunCommand> node) {
    vector<shared_ptr<Sort>> sig;
    sig.insert(sig.begin(), node->getParams().begin(), node->getParams().end());
    sig.push_back(node->getSort());

    return make_shared<FunInfo>(node->getSymbol()->toString(), sig, node);
}

shared_ptr<SortInfo> getInfo(shared_ptr<DeclareSortCommand> node) {
    return make_shared<SortInfo>(node->getSymbol()->toString(), node->getArity()->getValue(), node);
}

shared_ptr<FunInfo> getInfo(shared_ptr<DefineFunCommand> node) {
    vector<shared_ptr<Sort>> sig;
    vector<shared_ptr<SortedVariable>> &params = node->getDefinition()->getSignature()->getParams();
    for (vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        sig.push_back((*it)->getSort());
    }
    sig.push_back(node->getDefinition()->getSignature()->getSort());

    return make_shared<FunInfo>(node->getDefinition()->getSignature()->getSymbol()->toString(),
                                sig, node->getDefinition()->getBody(), node);
}

shared_ptr<FunInfo> getInfo(shared_ptr<DefineFunRecCommand> node) {
    vector<shared_ptr<Sort>> sig;
    vector<shared_ptr<SortedVariable>> &params = node->getDefinition()->getSignature()->getParams();
    for (vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        sig.push_back((*it)->getSort());
    }
    sig.push_back(node->getDefinition()->getSignature()->getSort());

    return make_shared<FunInfo>(node->getDefinition()->getSignature()->getSymbol()->toString(),
                                sig, node->getDefinition()->getBody(), node);
}

vector<shared_ptr<FunInfo>> getInfo(shared_ptr<DefineFunsRecCommand> node) {
    vector<shared_ptr<FunInfo>> infos;
    for (unsigned long i = 0; i < node->getDeclarations().size(); i++) {
        vector<shared_ptr<Sort>> sig;
        vector<shared_ptr<SortedVariable>> &params = node->getDeclarations()[i]->getParams();
        for (vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
            sig.push_back((*it)->getSort());
        }
        sig.push_back(node->getDeclarations()[i]->getSort());

        infos.push_back(make_shared<FunInfo>(node->getDeclarations()[i]->getSymbol()->toString(),
                                             sig, node->getBodies()[i], node));
    }

    return infos;
}

shared_ptr<SortInfo> getInfo(shared_ptr<DefineSortCommand> node) {
    return make_shared<SortInfo>(node->getSymbol()->toString(), node->getParams().size(),
                                 node->getParams(), node->getSort(), node);
}

shared_ptr<SortInfo> getInfo(shared_ptr<SortSymbolDeclaration> node) {
    return make_shared<SortInfo>(node->getIdentifier()->toString(),
                                 node->getArity()->getValue(),
                                 node->getAttributes(), node);
}

shared_ptr<FunInfo> getInfo(shared_ptr<SpecConstFunDeclaration> node) {
    vector<shared_ptr<Sort>> sig;
    sig.push_back(node->getSort());

    return make_shared<FunInfo>(node->getConstant()->toString(), sig, node->getAttributes(), node);
}

shared_ptr<FunInfo> getInfo(shared_ptr<MetaSpecConstFunDeclaration> node) {
    vector<shared_ptr<Sort>> sig;
    sig.push_back(node->getSort());

    return make_shared<FunInfo>(node->getConstant()->toString(), sig, node->getAttributes(), node);
}

shared_ptr<FunInfo> getInfo(shared_ptr<IdentifierFunDeclaration> node) {
    return make_shared<FunInfo>(node->getIdentifier()->toString(), node->getSignature(),
                                node->getAttributes(), node);
}

shared_ptr<FunInfo> getInfo(shared_ptr<ParametricFunDeclaration> node) {
    return make_shared<FunInfo>(node->getIdentifier()->toString(), node->getSignature(),
                                node->getParams(), node->getAttributes(), node);
}

bool SortednessChecker::equalSignatures(vector<shared_ptr<Sort>> &sig1, vector<shared_ptr<Sort>> &sig2) {
    if (sig1.size() != sig2.size())
        return false;

    for (unsigned long i = 0; i < sig1.size(); i++) {
        if (sig1[i]->toString() != sig2[i]->toString())
            return false;
    }

    return true;
}

bool SortednessChecker::equalParamSignatures(vector<shared_ptr<Symbol>> &params1,
                                             vector<shared_ptr<Sort>> &sig1,
                                             vector<shared_ptr<Symbol>> &params2,
                                             vector<shared_ptr<Sort>> &sig2) {
    if (params1.size() != params2.size() || sig1.size() != sig2.size())
        return false;

    unordered_map<string, string> mapping;
    for (unsigned long i = 0; i < sig1.size(); i++) {
        shared_ptr<Sort> sort1 = sig1[i];
        shared_ptr<Sort> sort2 = sig2[i];

        if (!equalParamSorts(params1, sort1, params2, sort2, mapping))
            return false;
    }

    return mapping.size() == params1.size();
}

bool SortednessChecker::equalParamSorts(vector<shared_ptr<Symbol>> &params1, shared_ptr<Sort> sort1,
                                        vector<shared_ptr<Symbol>> &params2, shared_ptr<Sort> sort2,
                                        unordered_map<string, string> &mapping) {

    if (sort1->getParams().size() != sort2->getParams().size())
        return false;

    if (sort1->getParams().size() == 0) {
        bool isParam1 = false;
        bool isParam2 = false;

        string str1 = sort1->toString();
        string str2 = sort2->toString();

        for (unsigned long j = 0; j < params1.size(); j++) {
            if (params1[j]->toString() == str1)
                isParam1 = true;
            if (params2[j]->toString() == str2)
                isParam2 = true;
        }

        if ((isParam1 && !isParam2) || (!isParam1 && isParam2)) {
            return false;
        } else if (isParam1) {
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
        if (sort1->getIdentifier()->toString() != sort2->getIdentifier()->toString())
            return false;

        for (unsigned long k = 0; k < sort1->getParams().size(); k++) {
            if (!equalParamSorts(params1, sort1->getParams()[k], params2, sort2->getParams()[k], mapping))
                return false;
        }

        return true;
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

void SortednessChecker::visit(shared_ptr<AssertCommand> node) { }

void SortednessChecker::visit(shared_ptr<DeclareConstCommand> node) {
    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Constant '" + nodeInfo->name + "' already exists", node, dupInfo);
    } else {
        arg->getTopLevel()->addFun(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<DeclareFunCommand> node) {
    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name + "' already exists with the same signature", node, dupInfo);
    } else {
        arg->getTopLevel()->addFun(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<DeclareSortCommand> node) {
    shared_ptr<SortInfo> nodeInfo = getInfo(node);
    shared_ptr<SortInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Sort symbol '" + nodeInfo->name + "' already exists", node, dupInfo);
    } else {
        arg->getTopLevel()->addSort(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<DefineFunCommand> node) {
    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name + "' already exists with the same signature", node, dupInfo);
    } else {
        arg->getTopLevel()->addFun(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<DefineFunRecCommand> node) {
    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name + "' already exists with the same signature", node, dupInfo);
    } else {
        arg->getTopLevel()->addFun(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<DefineFunsRecCommand> node) {
    vector<shared_ptr<FunInfo>> infos = getInfo(node);

    for (vector<shared_ptr<FunInfo>>::iterator it = infos.begin(); it != infos.end(); it++) {
        shared_ptr<FunInfo> dupInfo /* TODO = duplicate(decl.get())*/;
        if (dupInfo) {
            ret = false;
            addError("Function '" + (*it)->name + "' already exists with the same signature", node, *it);
        } else {
            arg->getTopLevel()->addFun(*it);
        }
    }
}

void SortednessChecker::visit(shared_ptr<DefineSortCommand> node) {
    shared_ptr<SortInfo> nodeInfo = getInfo(node);
    shared_ptr<SortInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Sort symbol '" + nodeInfo->name + "' already exists", node, dupInfo);
    } else {
        arg->getTopLevel()->addSort(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<GetValueCommand> node) { }

void SortednessChecker::visit(shared_ptr<PopCommand> node) { }

void SortednessChecker::visit(shared_ptr<PushCommand> node) { }

void SortednessChecker::visit(shared_ptr<ResetCommand> node) { }

void SortednessChecker::visit(shared_ptr<SetLogicCommand> node) {
    loadLogic(node->getLogic()->toString());
}

void SortednessChecker::visit(shared_ptr<FunctionDeclaration> node) { }

void SortednessChecker::visit(shared_ptr<FunctionDefinition> node) { }

void SortednessChecker::visit(shared_ptr<Identifier> node) { }

void SortednessChecker::visit(shared_ptr<QualifiedIdentifier> node) { }

void SortednessChecker::visit(shared_ptr<DecimalLiteral> node) { }

void SortednessChecker::visit(shared_ptr<NumeralLiteral> node) { }

void SortednessChecker::visit(shared_ptr<StringLiteral> node) { }

void SortednessChecker::visit(shared_ptr<Logic> node) {
    vector<shared_ptr<Attribute>> attrs = node->getAttributes();
    for (vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;
        if (attr->getKeyword()->getValue() == ":theories") {
            CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
            for (vector<shared_ptr<AttributeValue>>::iterator v = val->getValues().begin();
                 v != val->getValues().end(); v++) {
                string theory = dynamic_cast<Symbol *>((*v).get())->toString();
                loadTheory(theory);
            }
        }
    }
}

void SortednessChecker::visit(shared_ptr<Theory> node) {
    vector<shared_ptr<Attribute>> attrs = node->getAttributes();
    for (vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;

        if (attr->getKeyword()->getValue() == ":sorts" || attr->getKeyword()->getValue() == ":funs") {
            CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
            for (vector<shared_ptr<AttributeValue>>::iterator v = val->getValues().begin();
                 v != val->getValues().end(); v++) {
                (*v)->accept(this);
            }
        }
    }
}

void SortednessChecker::visit(shared_ptr<Script> node) {
    vector<shared_ptr<Command>> &commands = node->getCommands();
    for (vector<shared_ptr<Command>>::iterator it = commands.begin(); it != commands.end(); it++) {
        (*it)->accept(this);
    }
}

void SortednessChecker::visit(shared_ptr<Sort> node) { }

void SortednessChecker::visit(shared_ptr<CompSExpression> node) { }

void SortednessChecker::visit(shared_ptr<SortSymbolDeclaration> node) {
    shared_ptr<SortInfo> nodeInfo = getInfo(node);
    shared_ptr<SortInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Sort symbol '" + nodeInfo->name + "' already exists", node, dupInfo);
    } else {
        arg->getTopLevel()->addSort(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<SpecConstFunDeclaration> node) {
    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Specification constant '" + nodeInfo->name + "' already exists", node, dupInfo);
    } else {
        arg->getTopLevel()->addFun(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<MetaSpecConstFunDeclaration> node) {
    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Sort for meta specification constant '" + nodeInfo->name + "' already declared", node, dupInfo);
    } else {
        arg->getTopLevel()->addFun(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<IdentifierFunDeclaration> node) {
    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name + "' already existis with the same signature", node, dupInfo);
    } else {
        arg->getTopLevel()->addFun(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<ParametricFunDeclaration> node) {
    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo /* TODO = duplicate(decl.get())*/;

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name + "' already existis with the same signature", node, dupInfo);
    } else {
        arg->getTopLevel()->addFun(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<QualifiedTerm> node) { }

void SortednessChecker::visit(shared_ptr<LetTerm> node) { }

void SortednessChecker::visit(shared_ptr<ForallTerm> node) { }

void SortednessChecker::visit(shared_ptr<ExistsTerm> node) { }

void SortednessChecker::visit(shared_ptr<AnnotatedTerm> node) { }

void SortednessChecker::visit(shared_ptr<SortedVariable> node) { }

void SortednessChecker::visit(shared_ptr<VarBinding> node) { }

string SortednessChecker::getErrors() {
    stringstream ss;

    for (map<string, vector<shared_ptr<SortednessCheckError>>>::iterator it = errors.begin();
         it != errors.end(); it++) {
        string file = it->first;
        vector<shared_ptr<SortednessCheckError>> errs = it->second;

        ss << "In file '" << file << "'" << endl;

        for (vector<shared_ptr<SortednessCheckError>>::iterator itt = errs.begin(); itt != errs.end(); itt++) {
            shared_ptr<SortednessCheckError> err = *itt;
            ss << err->node->getRowLeft() << ":" << err->node->getColLeft()
            << " - " << err->node->getRowRight() << ":" << err->node->getColRight() << "   ";

            string nodestr = err->node->toString();
            if (nodestr.length() > 100)
                ss << string(nodestr, 100);
            else
                ss << nodestr;

            ss << endl;

            for (vector<shared_ptr<SortednessCheckErrorInfo>>::iterator info = err->infos.begin();
                 info != err->infos.end(); info++) {
                ss << "\t" << (*info)->message << endl;

                shared_ptr<AstNode> source;

                if ((*info)->sortInfo) {
                    source = (*info)->sortInfo->source;
                } else if ((*info)->funInfo) {
                    source = (*info)->funInfo->source;
                }

                if (source) {
                    ss << "\t\tPreviously, in file '" << source->getFilename()->c_str() << "'\n\t\t"
                    << source->getRowLeft() << ":" << source->getColLeft() << " - "
                    << source->getRowRight() << ":" << source->getColRight() << "   ";

                    string sourcestr = source->toString();
                    if (sourcestr.length() > 100)
                        ss << string(sourcestr, 100);
                    else
                        ss << sourcestr;
                }

                ss << endl;
            }
        }
    }

    ss << endl;

    return ss.str();
}