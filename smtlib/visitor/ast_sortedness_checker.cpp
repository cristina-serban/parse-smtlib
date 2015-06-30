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

shared_ptr<SortInfo> SortednessChecker::getInfo(shared_ptr<DeclareSortCommand> node) {
    return make_shared<SortInfo>(node->getSymbol()->toString(), node->getArity()->getValue(), node);
}

shared_ptr<SortInfo> SortednessChecker::getInfo(shared_ptr<DefineSortCommand> node) {
    return make_shared<SortInfo>(node->getSymbol()->toString(), node->getParams().size(),
                                 node->getParams(), arg->expand(node->getSort()), node);
}


shared_ptr<SortInfo> SortednessChecker::getInfo(shared_ptr<SortSymbolDeclaration> node) {
    return make_shared<SortInfo>(node->getIdentifier()->toString(),
                                 node->getArity()->getValue(),
                                 node->getAttributes(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<SpecConstFunDeclaration> node) {
    vector<shared_ptr<Sort>> sig;
    sig.push_back(arg->expand(node->getSort()));

    return make_shared<FunInfo>(node->getConstant()->toString(), sig, node->getAttributes(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<MetaSpecConstFunDeclaration> node) {
    vector<shared_ptr<Sort>> sig;
    sig.push_back(arg->expand(node->getSort()));
    return make_shared<FunInfo>(node->getConstant()->toString(), sig, node->getAttributes(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<IdentifierFunDeclaration> node) {
    vector<shared_ptr<Sort>> &sig = node->getSignature();
    vector<shared_ptr<Sort>> newsig;

    for (vector<shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
        newsig.push_back(arg->expand(*it));
    }

    return make_shared<FunInfo>(node->getIdentifier()->toString(), newsig,
                                node->getAttributes(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<ParametricFunDeclaration> node) {
    vector<shared_ptr<Sort>> &sig = node->getSignature();
    vector<shared_ptr<Sort>> newsig;

    for (vector<shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
        newsig.push_back(arg->expand(*it));
    }

    return make_shared<FunInfo>(node->getIdentifier()->toString(), newsig,
                                node->getParams(), node->getAttributes(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<DeclareConstCommand> node) {
    vector<shared_ptr<Sort>> sig;
    sig.push_back(arg->expand(node->getSort()));

    return make_shared<FunInfo>(node->getSymbol()->toString(), sig, node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<DeclareFunCommand> node) {
    vector<shared_ptr<Sort>> &sig = node->getParams();
    vector<shared_ptr<Sort>> newsig;

    for (vector<shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
        shared_ptr<Sort> itsort = arg->expand(*it);
        newsig.push_back(itsort);
    }
    shared_ptr<Sort> retsort = arg->expand(node->getSort());
    newsig.push_back(retsort);

    return make_shared<FunInfo>(node->getSymbol()->toString(), newsig, node);
}

shared_ptr<FunInfo>SortednessChecker::getInfo(shared_ptr<DefineFunCommand> node) {
    vector<shared_ptr<Sort>> newsig;
    vector<shared_ptr<SortedVariable>> &params = node->getDefinition()->getSignature()->getParams();
    for (vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        newsig.push_back(arg->expand((*it)->getSort()));
    }
    newsig.push_back(arg->expand(node->getDefinition()->getSignature()->getSort()));

    return make_shared<FunInfo>(node->getDefinition()->getSignature()->getSymbol()->toString(),
                                newsig, node->getDefinition()->getBody(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<DefineFunRecCommand> node) {
    vector<shared_ptr<Sort>> newsig;
    vector<shared_ptr<SortedVariable>> &params = node->getDefinition()->getSignature()->getParams();
    for (vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        newsig.push_back(arg->expand((*it)->getSort()));
    }
    newsig.push_back(arg->expand(node->getDefinition()->getSignature()->getSort()));

    return make_shared<FunInfo>(node->getDefinition()->getSignature()->getSymbol()->toString(),
                                newsig, node->getDefinition()->getBody(), node);
}

vector<shared_ptr<FunInfo>> SortednessChecker::getInfo(shared_ptr<DefineFunsRecCommand> node) {
    vector<shared_ptr<FunInfo>> infos;
    for (unsigned long i = 0; i < node->getDeclarations().size(); i++) {
        vector<shared_ptr<Sort>> newsig;
        vector<shared_ptr<SortedVariable>> &params = node->getDeclarations()[i]->getParams();
        for (vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
            newsig.push_back(arg->expand((*it)->getSort()));
        }
        newsig.push_back(arg->expand(node->getDeclarations()[i]->getSort()));

        infos.push_back(make_shared<FunInfo>(node->getDeclarations()[i]->getSymbol()->toString(),
                                             newsig, node->getBodies()[i], node));
    }

    return infos;
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

shared_ptr<SortednessChecker::SortednessCheckError>
SortednessChecker::checkSort(shared_ptr<Sort> sort,
                             shared_ptr<AstNode> source,
                             shared_ptr<SortednessChecker::SortednessCheckError> err) {
    string name = sort->getIdentifier()->toString();
    shared_ptr<SortInfo> info = arg->getSortInfo(name);
    if (!info) {
        stringstream ss;
        ss << "Sort '" << name << "' does not exist ("
        << sort->getRowLeft() << ":" << sort->getColLeft() << " - "
        << sort->getRowRight() << ":" << sort->getColRight() << ")";
        err = addError(ss.str(), source, err);
        ret = false;
    } else {
        if (sort->getArgs().size() != info->arity) {
            stringstream ss;
            ss << "Sort '" << name << "' should have an arity of " << info->arity
            << ", not " << sort->getArgs().size() << " ("
            << sort->getRowLeft() << ":" << sort->getColLeft() << " - "
            << sort->getRowRight() << ":" << sort->getColRight() << ")";
            err = addError(ss.str(), source, info, err);
            ret = false;
        } else {
            for (vector<shared_ptr<Sort>>::iterator it = sort->getArgs().begin();
                 it != sort->getArgs().end(); it++) {
                checkSort(*it, source, err);
            }
        }
    }
    return err;
}

shared_ptr<SortednessChecker::SortednessCheckError>
SortednessChecker::checkSort(vector<shared_ptr<Symbol>> params,
                             unordered_map<string, bool> &paramUsage,
                             shared_ptr<Sort> sort,
                             shared_ptr<AstNode> source,
                             shared_ptr<SortednessChecker::SortednessCheckError> err) {
    string name = sort->getIdentifier()->toString();
    bool isParam = false;
    for (vector<shared_ptr<Symbol>>::iterator it = params.begin(); it != params.end(); it++) {
        if (name == (*it)->toString())
            isParam = true;
    }

    if (isParam) {
        paramUsage[name] = true;

        if (!sort->getArgs().empty()) {
            ret = false;
            err = addError(sort->toString() + ": '" + name +
                           "' is a sort parameter - it should have an arity of 0 ", source, err);
        }
    } else {
        shared_ptr<SortInfo> info = arg->getSortInfo(name);
        if (!info) {
            stringstream ss;
            ss << "Sort '" << name << "' does not exist ("
            << sort->getRowLeft() << ":" << sort->getColLeft() << " - "
            << sort->getRowRight() << ":" << sort->getColRight() << ")";
            err = addError(ss.str(), source, err);
            ret = false;
        } else {
            if (sort->getArgs().size() != info->arity) {
                stringstream ss;
                ss << "Sort '" << name << "' should have an arity of " << info->arity
                << ", not " << sort->getArgs().size() << " ("
                << sort->getRowLeft() << ":" << sort->getColLeft() << " - "
                << sort->getRowRight() << ":" << sort->getColRight() << ")";
                err = addError(ss.str(), source, info, err);
                ret = false;
            } else {
                for (vector<shared_ptr<Sort>>::iterator it = sort->getArgs().begin();
                     it != sort->getArgs().end(); it++) {
                    checkSort(params, paramUsage, *it, source, err);
                }
            }
        }
    }
    return err;
}

void SortednessChecker::visit(shared_ptr<AssertCommand> node) {
    TermSorter sorter;
    shared_ptr<Sort> result = sorter.run(make_shared<TermSorterInfo>(arg, this, node),
                                         node->getTerm());
    if (result) {
        string resstr = result->toString();
        if (resstr != "Bool") {
            stringstream ss;
            ss << "Assertion term '";
            string termstr = node->getTerm()->toString();
            if (termstr.length() > 50) {
                ss << string(termstr, 50) << "[...]";
            } else {
                ss << termstr;
            }
            ss << "' (" << node->getTerm()->getRowLeft() << ":" << node->getTerm()->getColLeft() << " - "
            << node->getTerm()->getRowRight() << ":" << node->getTerm()->getColRight()
            << ") is of type " << resstr << ", not Bool";
            addError(ss.str(), node);
            ret = false;
        }
    } else {
        stringstream ss;
        ss << "Assertion term '";
        string termstr = node->getTerm()->toString();
        if (termstr.length() > 50) {
            ss << string(termstr, 50) << "[...]";
        } else {
            ss << termstr;
        }
        ss << "' (" << node->getTerm()->getRowLeft() << ":" << node->getTerm()->getColLeft() << " - "
        << node->getTerm()->getRowRight() << ":" << node->getTerm()->getColRight()
        << ") is not well-sorted";
        addError(ss.str(), node);
        ret = false;
    }
}

void SortednessChecker::visit(shared_ptr<DeclareConstCommand> node) {
    shared_ptr<SortednessCheckError> err;
    err = checkSort(node->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = arg->tryAdd(nodeInfo);

    if (dupInfo) {
        ret = false;
        addError("Constant '" + nodeInfo->name + "' already exists", node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<DeclareFunCommand> node) {
    shared_ptr<SortednessCheckError> err;

    for (vector<shared_ptr<Sort>>::iterator it = node->getParams().begin(); it != node->getParams().end(); it++) {
        err = checkSort(*it, node, err);
    }
    err = checkSort(node->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = arg->tryAdd(nodeInfo);

    shared_ptr<Sort> retsort = nodeInfo->signature[nodeInfo->signature.size() - 1];

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name + "' already exists with the same signature", node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<DeclareSortCommand> node) {
    shared_ptr<SortInfo> nodeInfo = getInfo(node);
    shared_ptr<SortInfo> dupInfo = arg->tryAdd(nodeInfo);

    if (dupInfo) {
        ret = false;
        addError("Sort symbol '" + nodeInfo->name + "' already exists", node, dupInfo);
    }
}

// TODO Check that all parameters are used inside function
void SortednessChecker::visit(shared_ptr<DefineFunCommand> node) {
    shared_ptr<SortednessCheckError> err;

    vector<shared_ptr<SortedVariable>> sig = node->getDefinition()->getSignature()->getParams();
    for (vector<shared_ptr<SortedVariable>>::iterator it = sig.begin(); it != sig.end(); it++) {
        err = checkSort((*it)->getSort(), node, err);
    }
    err = checkSort(node->getDefinition()->getSignature()->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = arg->findDuplicate(nodeInfo);

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name + "' already exists with the same signature", node, dupInfo, err);
    } else {
        bool ok = true;
        arg->push();

        vector<shared_ptr<SortedVariable>> &bindings = node->getDefinition()->getSignature()->getParams();
        for (auto it : bindings) {
            arg->tryAdd(make_shared<VarInfo>(it->getSymbol()->toString(),
                                             arg->expand(it->getSort()), node));
        }

        TermSorter sorter;
        shared_ptr<Sort> result = sorter.run(make_shared<TermSorterInfo>(arg, this, node),
                                             node->getDefinition()->getBody());

        if (result) {
            string retstr = nodeInfo->signature[nodeInfo->signature.size() - 1]->toString();
            string resstr = result->toString();
            if (resstr != retstr) {
                stringstream ss;
                ss << "Function body '";
                string termstr = node->getDefinition()->getBody()->toString();
                if (termstr.length() > 50) {
                    ss << string(termstr, 50) << "[...]";
                } else {
                    ss << termstr;
                }
                ss << "' (" << node->getDefinition()->getBody()->getRowLeft() << ":"
                << node->getDefinition()->getBody()->getColLeft() << " - "
                << node->getDefinition()->getBody()->getRowRight() << ":"
                << node->getDefinition()->getBody()->getColRight()
                << ") is of type " << resstr << ", not " << retstr;
                addError(ss.str(), node);

                ret = false;
                ok = false;
            }
        } else {
            stringstream ss;
            ss << "Function body '";
            string termstr = node->getDefinition()->getBody()->toString();
            if (termstr.length() > 50) {
                ss << string(termstr, 50) << "[...]";
            } else {
                ss << termstr;
            }
            ss << "' (" << node->getDefinition()->getBody()->getRowLeft() << ":"
            << node->getDefinition()->getBody()->getColLeft() << " - "
            << node->getDefinition()->getBody()->getRowRight() << ":"
            << node->getDefinition()->getBody()->getColRight()
            << ") is not well-sorted";
            addError(ss.str(), node);

            ret = false;
            ok = false;
        }

        arg->pop();
        if (ok)
            arg->tryAdd(nodeInfo);
    }
}

// TODO Check that all parameters are used inside function
void SortednessChecker::visit(shared_ptr<DefineFunRecCommand> node) {
    shared_ptr<SortednessCheckError> err;

    vector<shared_ptr<SortedVariable>> sig = node->getDefinition()->getSignature()->getParams();
    for (vector<shared_ptr<SortedVariable>>::iterator it = sig.begin(); it != sig.end(); it++) {
        err = checkSort((*it)->getSort(), node, err);
    }
    err = checkSort(node->getDefinition()->getSignature()->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = arg->findDuplicate(nodeInfo);

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name + "' already exists with the same signature", node, dupInfo, err);
    } else {
        bool ok = true;
        arg->push();
        arg->tryAdd(nodeInfo);

        vector<shared_ptr<SortedVariable>> &bindings = node->getDefinition()->getSignature()->getParams();
        for (auto it : bindings) {
            arg->tryAdd(make_shared<VarInfo>(it->getSymbol()->toString(),
                                             arg->expand(it->getSort()), node));
        }

        TermSorter sorter;
        shared_ptr<Sort> result = sorter.run(make_shared<TermSorterInfo>(arg, this, node),
                                             node->getDefinition()->getBody());

        if (result) {
            string retstr = nodeInfo->signature[nodeInfo->signature.size() - 1]->toString();
            string resstr = result->toString();
            if (resstr != retstr) {
                stringstream ss;
                ss << "Function body '";
                string termstr = node->getDefinition()->getBody()->toString();
                if (termstr.length() > 50) {
                    ss << string(termstr, 50) << "[...]";
                } else {
                    ss << termstr;
                }
                ss << "' (" << node->getDefinition()->getBody()->getRowLeft() << ":"
                << node->getDefinition()->getBody()->getColLeft() << " - "
                << node->getDefinition()->getBody()->getRowRight() << ":"
                << node->getDefinition()->getBody()->getColRight()
                << ") is of type " << resstr << ", not " << retstr;
                addError(ss.str(), node);

                ret = false;
                ok = false;
            }
        } else {
            stringstream ss;
            ss << "Function body '";
            string termstr = node->getDefinition()->getBody()->toString();
            if (termstr.length() > 50) {
                ss << string(termstr, 50) << "[...]";
            } else {
                ss << termstr;
            }
            ss << "' (" << node->getDefinition()->getBody()->getRowLeft() << ":"
            << node->getDefinition()->getBody()->getColLeft() << " - "
            << node->getDefinition()->getBody()->getRowRight() << ":"
            << node->getDefinition()->getBody()->getColRight()
            << ") is not well-sorted";
            addError(ss.str(), node);

            ret = false;
            ok = false;
        }

        arg->pop();
        if (ok)
            arg->tryAdd(nodeInfo);
    }
}

// TODO Check that all parameters are used inside function
void SortednessChecker::visit(shared_ptr<DefineFunsRecCommand> node) {
    shared_ptr<SortednessCheckError> err;
    vector<shared_ptr<FunctionDeclaration>> &decls = node->getDeclarations();
    vector<shared_ptr<Term>> &bodies = node->getBodies();

    for (vector<shared_ptr<FunctionDeclaration>>::iterator it = decls.begin(); it != decls.end(); it++) {

        vector<shared_ptr<SortedVariable>> sig = (*it)->getParams();
        for (vector<shared_ptr<SortedVariable>>::iterator itt = sig.begin(); itt != sig.end(); itt++) {
            err = checkSort((*itt)->getSort(), node, err);
        }
        err = checkSort((*it)->getSort(), node, err);
    }

    vector<shared_ptr<FunInfo>> infos = getInfo(node);

    bool dup = false;
    for (vector<shared_ptr<FunInfo>>::iterator it = infos.begin(); it != infos.end(); it++) {
        shared_ptr<FunInfo> dupInfo = arg->findDuplicate(*it);
        if (dupInfo) {
            dup = true;
            ret = false;
            err = addError("Function '" + (*it)->name + "' already exists with the same signature", node, *it, err);
        }
    }

    if (!dup) {
        bool ok = true;
        arg->push();

        for (unsigned long i = 0; i < decls.size(); i++) {
            arg->tryAdd(infos[i]);
        }

        for (unsigned long i = 0; i < decls.size(); i++) {
            arg->push();
            vector<shared_ptr<SortedVariable>> &bindings = decls[i]->getParams();
            for (auto it : bindings) {
                arg->tryAdd(make_shared<VarInfo>(it->getSymbol()->toString(),
                                                 arg->expand(it->getSort()), node));
            }

            TermSorter sorter;
            shared_ptr<Sort> result = sorter.run(make_shared<TermSorterInfo>(arg, this, node),
                                                 bodies[i]);

            if (result) {
                string retstr = infos[i]->signature[infos[i]->signature.size() - 1]->toString();
                string resstr = result->toString();
                if (resstr != retstr) {
                    stringstream ss;
                    ss << "The body of function " << infos[i]->name << ", '";
                    string termstr = infos[i]->body->toString();
                    if (termstr.length() > 50) {
                        ss << string(termstr, 50) << "[...]";
                    } else {
                        ss << termstr;
                    }
                    ss << "' (" << infos[i]->body->getRowLeft() << ":"
                    << infos[i]->body->getColLeft() << " - "
                    << infos[i]->body->getRowRight() << ":"
                    << infos[i]->body->getColRight()
                    << "), is of type " << resstr << ", not " << retstr;
                    err = addError(ss.str(), node, err);

                    ret = false;
                    ok = false;
                }
            } else {
                stringstream ss;
                ss << "The body of function " << infos[i]->name << ", '";
                string termstr = infos[i]->body->toString();
                if (termstr.length() > 50) {
                    ss << string(termstr, 50) << "[...]";
                } else {
                    ss << termstr;
                }
                ss << "' (" << infos[i]->body->getRowLeft() << ":"
                << infos[i]->body->getColLeft() << " - "
                << infos[i]->body->getRowRight() << ":"
                << infos[i]->body->getColRight()
                << "), is not well-sorted";
                err = addError(ss.str(), node, err);

                ret = false;
                ok = false;
            }
            arg->pop();
        }

        arg->pop();

        if (ok) {
            for (unsigned long i = 0; i < infos.size(); i++) {
                arg->tryAdd(infos[i]);
            }
        }
    }
}

void SortednessChecker::visit(shared_ptr<DefineSortCommand> node) {
    shared_ptr<SortednessCheckError> err;
    unordered_map<string, bool> paramUsage;

    err = checkSort(node->getParams(), paramUsage, node->getSort(), node, err);

    if (paramUsage.size() != node->getParams().size()) {
        long diff = node->getParams().size() - paramUsage.size();

        stringstream ss;
        ss << "Sort parameter" << ((diff == 1) ? " " : "s ");
        bool first = true;
        for (vector<shared_ptr<Symbol>>::iterator it = node->getParams().begin();
             it != node->getParams().end(); it++) {
            string pname = (*it)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                if (!first) {
                    ss << ", ";
                } else {
                    first = false;
                }
                ss << "'" << pname << "'";
            }
        }
        ss << ((diff == 1) ? " is " : " are ") << "not used in sort definition.";
        ret = false;
        shared_ptr<SortInfo> null;
        err = addError(ss.str(), node, null, err);
    }

    shared_ptr<SortInfo> nodeInfo = getInfo(node);
    shared_ptr<SortInfo> dupInfo = arg->tryAdd(nodeInfo);

    if (dupInfo) {
        ret = false;
        addError("Sort symbol '" + nodeInfo->name + "' already exists", node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<GetValueCommand> node) {
    shared_ptr<SortednessCheckError> err;
    for (vector<shared_ptr<Term>>::iterator it = node->getTerms().begin(); it != node->getTerms().end(); it++) {
        TermSorter sorter;
        shared_ptr<Sort> result = sorter.run(make_shared<TermSorterInfo>(arg, this, node), *it);
        if (!result) {
            stringstream ss;
            ss << "Term '";
            string termstr = (*it)->toString();
            if (termstr.length() > 50) {
                ss << string(termstr, 50) << "[...]";
            } else {
                ss << termstr;
            }
            ss << "' (" << (*it)->getRowLeft() << ":" << (*it)->getColLeft() << " - "
            << (*it)->getRowRight() << ":" << (*it)->getColRight()
            << ") is not well-sorted";
            err = addError(ss.str(), node, err);
            ret = false;
        }
    }
}

void SortednessChecker::visit(shared_ptr<PopCommand> node) {
    unsigned long levels = (unsigned long) node->getNumeral()->getValue();
    if (!arg->pop(levels)) {
        stringstream ss;
        ss << "Stack not deep enough to pop " << levels;
        if (levels == 1)
            ss << " level";
        else
            ss << " levels";
        addError(ss.str(), node);
    }
}

void SortednessChecker::visit(shared_ptr<PushCommand> node) {
    arg->push((unsigned long) node->getNumeral()->getValue());
}

void SortednessChecker::visit(shared_ptr<ResetCommand> node) {
    arg->reset();
}

void SortednessChecker::visit(shared_ptr<SetLogicCommand> node) {
    loadLogic(node->getLogic()->toString());
}

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

void SortednessChecker::visit(shared_ptr<SortSymbolDeclaration> node) {
    shared_ptr<SortInfo> nodeInfo = getInfo(node);
    shared_ptr<SortInfo> dupInfo = arg->tryAdd(nodeInfo);

    if (dupInfo) {
        ret = false;
        addError("Sort symbol '" + nodeInfo->name + "' already exists", node, dupInfo);
    }
}

void SortednessChecker::visit(shared_ptr<SpecConstFunDeclaration> node) {
    shared_ptr<SortednessCheckError> err;
    err = checkSort(node->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = arg->tryAdd(nodeInfo);

    if (dupInfo) {
        ret = false;
        addError("Specification constant '" + nodeInfo->name + "' already exists", node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<MetaSpecConstFunDeclaration> node) {
    shared_ptr<SortednessCheckError> err;
    err = checkSort(node->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    vector<shared_ptr<FunInfo>> dupInfo = arg->getFunInfo(nodeInfo->name);

    if (!dupInfo.empty()) {
        ret = false;
        addError("Sort for meta specification constant '" +
                 nodeInfo->name + "' already declared", node, dupInfo[0], err);
    } else {
        arg->tryAdd(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<IdentifierFunDeclaration> node) {
    shared_ptr<SortednessCheckError> err;

    vector<shared_ptr<Sort>> sig = node->getSignature();
    for (vector<shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
        err = checkSort(*it, node, err);
    }

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = arg->tryAdd(nodeInfo);

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name +
                 "' already existis with the same signature", node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<ParametricFunDeclaration> node) {
    shared_ptr<SortednessCheckError> err;
    unordered_map<string, bool> paramUsage;

    vector<shared_ptr<Sort>> sig = node->getSignature();
    for (vector<shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
        err = checkSort(node->getParams(), paramUsage, *it, node, err);
    }

    shared_ptr<FunInfo> nodeInfo = getInfo(node);

    if (paramUsage.size() != node->getParams().size()) {
        long diff = node->getParams().size() - paramUsage.size();

        stringstream ss;
        ss << "Sort parameter" << ((diff == 1) ? " " : "s ");
        bool first = true;
        for (vector<shared_ptr<Symbol>>::iterator it = node->getParams().begin();
             it != node->getParams().end(); it++) {
            string pname = (*it)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                if (!first) {
                    ss << ", ";
                } else {
                    first = false;
                }
                ss << "'" << pname << "'";
            }
        }
        ss << ((diff == 1) ? " is " : " are ") << "not used in parametric function declaration.";
        ret = false;
        err = addError(ss.str(), node, err);
    }

    shared_ptr<FunInfo> dupInfo = arg->tryAdd(nodeInfo);

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name +
                 "' already existis with the same signature", node, dupInfo, err);
    }
}

string SortednessChecker::getErrors() {
    stringstream ss;

    for (map<string, vector<shared_ptr<SortednessCheckError>>>::iterator it = errors.begin();
         it != errors.end(); it++) {
        string file = it->first;
        vector<shared_ptr<SortednessCheckError>> errs = it->second;

        long length = 11 + file.length();
        for (long i = 0; i < length; i++)
            ss << "-";
        ss << endl << "In file '" << file << "':" << endl;
        for (long i = 0; i < length; i++)
            ss << "-";
        ss << endl;

        for (vector<shared_ptr<SortednessCheckError>>::iterator itt = errs.begin(); itt != errs.end(); itt++) {
            shared_ptr<SortednessCheckError> err = *itt;
            ss << err->node->getRowLeft() << ":" << err->node->getColLeft()
            << " - " << err->node->getRowRight() << ":" << err->node->getColRight() << "   ";

            string nodestr = err->node->toString();
            if (nodestr.length() > 100)
                ss << string(nodestr, 100) << "[...]";
            else
                ss << nodestr;

            ss << endl;

            for (vector<shared_ptr<SortednessCheckErrorInfo>>::iterator info = err->infos.begin();
                 info != err->infos.end(); info++) {
                shared_ptr<AstNode> source;

                if ((*info)->sortInfo) {
                    source = (*info)->sortInfo->source;
                } else if ((*info)->funInfo) {
                    source = (*info)->funInfo->source;
                }

                if (info != err->infos.begin() && source)
                    ss << endl;

                ss << "\t" << (*info)->message << "." << endl;

                if (source) {
                    ss << "\t\tPreviously, in file '" << source->getFilename()->c_str() << "'\n\t\t"
                    << source->getRowLeft() << ":" << source->getColLeft() << " - "
                    << source->getRowRight() << ":" << source->getColRight() << "   ";

                    string sourcestr = source->toString();
                    if (sourcestr.length() > 100)
                        ss << string(sourcestr, 100);
                    else
                        ss << sourcestr;

                    ss << endl;

                    if (info + 1 != err->infos.end())
                        ss << endl;
                }
            }

            ss << endl;
        }
    }

    ss << endl;

    return ss.str();
}

void SortednessChecker::TermSorter::visit(std::shared_ptr<Identifier> node) {
    shared_ptr<VarInfo> varInfo = arg->stack->getVarInfo(node->toString());
    if (varInfo) {
        ret = varInfo->sort;
    } else {
        vector<shared_ptr<FunInfo>> infos = arg->stack->getFunInfo(node->toString());
        vector<shared_ptr<Sort>> possibleSorts;
        for (auto it : infos) {
            if (it->signature.size() == 1 && it->params.empty())
                possibleSorts.push_back(it->signature[0]);
        }

        if (possibleSorts.size() == 1) {
            ret = possibleSorts[0];
        } else if (possibleSorts.empty()) {
            arg->checker->addError("Unknown constant '" + node->toString() + "'", node);
        } else {
            stringstream ss;
            ss << "Multiple possible sorts for constant '" << node->toString() << "': ";
            bool first = true;
            for (auto it : possibleSorts) {
                if (!first)
                    ss << ", ";
                else
                    first = false;
                ss << it->toString();
            }
            arg->checker->addError(ss.str(), node);
        }
    }
}

void SortednessChecker::TermSorter::visit(std::shared_ptr<QualifiedIdentifier> node) {
    vector<shared_ptr<FunInfo>> infos = arg->stack->getFunInfo(node->getIdentifier()->toString());
    vector<shared_ptr<Sort>> retSorts;
    for (auto it : infos) {
        if (it->signature.size() == 1 && it->params.empty())
            retSorts.push_back(it->signature[0]);
    }

    shared_ptr<Sort> expanded = arg->stack->expand(node->getSort());

    if (retSorts.size() == 1 && retSorts[0]->toString() == expanded->toString()) {
        ret = retSorts[0];
    } else {
        if (retSorts.empty()) {
            arg->checker->addError("Unknown constant '" + node->getIdentifier()->toString() + "'", node);
        } else {
            stringstream ss;
            ss << "Constant '" << node->getIdentifier()->toString() << "' cannot be of sort " << expanded->toString()
            << ". Possible sorts: ";
            bool first = true;
            for (auto it : retSorts) {
                if (!first)
                    ss << ", ";
                else
                    first = false;
                ss << it->toString();
            }
            arg->checker->addError(ss.str(), node);
        }
    }
}

void SortednessChecker::TermSorter::visit(std::shared_ptr<DecimalLiteral> node) {
    vector<shared_ptr<FunInfo>> infos = arg->stack->getFunInfo("DECIMAL");
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        if (infos.empty())
            arg->checker->addError("No declared sort for decimal literals", node);
        else
            arg->checker->addError("Multiple declared sorts for decimal literals", node);
    }
}

void SortednessChecker::TermSorter::visit(std::shared_ptr<NumeralLiteral> node) {
    vector<shared_ptr<FunInfo>> infos = arg->stack->getFunInfo("NUMERAL");
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        if (infos.empty())
            arg->checker->addError("No declared sort for numeral literals", node);
        else
            arg->checker->addError("Multiple declared sorts for numeral literals", node);
    }
}

void SortednessChecker::TermSorter::visit(std::shared_ptr<StringLiteral> node) {
    vector<shared_ptr<FunInfo>> infos = arg->stack->getFunInfo("STRING");
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        if (infos.empty())
            arg->checker->addError("No declared sort for string literals", node);
        else
            arg->checker->addError("Multiple declared sorts for string literals", node);
    }
}

void SortednessChecker::TermSorter::visit(std::shared_ptr<QualifiedTerm> node) {
    vector<shared_ptr<Sort>> argSorts;
    for (vector<shared_ptr<Term>>::iterator it = node->getTerms().begin();
         it != node->getTerms().end(); it++) {
        TermSorter sorter;
        shared_ptr<Sort> result = sorter.run(arg, *it);
        if (result)
            argSorts.push_back(result);
        else {
            stringstream ss;
            ss << "Term '";
            string termstr = (*it)->toString();
            if (termstr.length() > 50) {
                ss << string(termstr, 50) << "[...]";
            } else {
                ss << termstr;
            }
            ss << "' (" << (*it)->getRowLeft() << ":" << (*it)->getColLeft() << " - "
            << (*it)->getRowRight() << ":" << (*it)->getColRight() << ") is not well-sorted";
            arg->checker->addError(ss.str(), node);
            ret = false;
            return;
        }
    }

    shared_ptr<Identifier> id = dynamic_pointer_cast<Identifier>(node->getIdentifier());
    shared_ptr<QualifiedIdentifier> qid = dynamic_pointer_cast<QualifiedIdentifier>(node->getIdentifier());

    shared_ptr<Sort> retExpanded;
    string name;

    if (id) {
        name = id->toString();
    } else {
        name = qid->getIdentifier()->toString();
        retExpanded = arg->stack->expand(qid->getSort());
    }

    vector<shared_ptr<FunInfo>> infos = arg->stack->getFunInfo(name);
    vector<shared_ptr<Sort>> retSorts;

    for (auto it : infos) {
        if (argSorts.size() == it->signature.size() - 1) {
            bool fits = true;
            if (it->params.empty()) {
                for (unsigned long i = 0; i < it->signature.size() - 1; i++) {
                    if (it->signature[i]->toString() != argSorts[i]->toString())
                        fits = false;
                }

                if (id) {
                    if (fits)
                        retSorts.push_back(it->signature[it->signature.size() - 1]);
                } else {
                    shared_ptr<Sort> retSort = it->signature[it->signature.size() - 1];
                    if (fits && retSort->toString() == retExpanded->toString()) {
                        ret = retSort;
                        return;
                    }
                }
            } else {
                vector<string> pnames;
                for (auto p : it->params) {
                    pnames.push_back(p->toString());
                }
                unordered_map<string, shared_ptr<Sort>> mapping;

                for (unsigned long i = 0; i < it->signature.size() - 1; i++) {
                    string pcurrent = it->signature[i]->toString();
                    if (find(pnames.begin(), pnames.end(), pcurrent) != pnames.end()) {
                        if (mapping.find(pcurrent) != mapping.end()) {
                            if (mapping[pcurrent]->toString() != argSorts[i]->toString())
                                fits = false;
                        } else {
                            mapping[pcurrent] = argSorts[i];
                        }
                    } else {
                        if (it->signature[i]->toString() != argSorts[i]->toString())
                            fits = false;
                    }
                }

                if (fits && mapping.size() == it->params.size()) {
                    shared_ptr<Sort> retSort = it->signature[it->signature.size() - 1];
                    string retSortString = retSort->toString();
                    if (find(pnames.begin(), pnames.end(), retSortString) != pnames.end()) {
                        if (id) {
                            retSorts.push_back(mapping[retSortString]);
                        } else {
                            if (mapping[retSortString]->toString() == arg->stack->expand(qid->getSort())->toString()) {
                                ret = mapping[retSortString];
                                return;
                            }
                        }
                    } else {
                        if (id) {
                            retSorts.push_back(retSort);
                        } else {
                            if (retSortString == arg->stack->expand(qid->getSort())->toString()) {
                                ret = retSort;
                                return;
                            }
                        }
                    }
                }
            }
        }
    }

    if (id) {
        if (retSorts.size() == 1) {
            ret = retSorts[0];
        } else if(retSorts.size() == 0) {
            stringstream ss;
            ss << "No known declaration for function '" << name << "' with parameter sorts (";
            bool first = true;
            for(auto it : argSorts) {
                if(first) {
                    first = false;
                } else {
                    ss << " ";
                }
                ss << it->toString();
            }
            ss << ")";
            arg->checker->addError(ss.str(), node);
        } else {
            stringstream ss;
            ss << "Multiple declarations for function '" << name << "' with parameter sorts ";
            bool first = true;
            for(auto it : argSorts) {
                if(first) {
                    first = false;
                } else {
                    ss << ", ";
                }
                ss << it->toString();
            }

            ss << ". Possible return sorts: ";
            first = true;
            for(auto it : retSorts) {
                if(first) {
                    first = false;
                } else {
                    ss << ", ";
                }
                ss << it->toString();
            }
            arg->checker->addError(ss.str(), node);
        }
    } else {
        stringstream ss;
        ss << "No known declaration for function '" << name << "' with parameter sorts ";
        bool first = true;
        for(auto it : argSorts) {
            if(first) {
                first = false;
            } else {
                ss << ", ";
            }
            ss << it->toString();
        }
        ss << " and return sort " << retExpanded->toString();
        arg->checker->addError(ss.str(), node);
    }
}

void SortednessChecker::TermSorter::visit(std::shared_ptr<LetTerm> node) {
    arg->stack->push();

    vector<shared_ptr<VarBinding>> &bindings = node->getBindings();
    for (auto it : bindings) {
        TermSorter sorter;
        shared_ptr<Sort> result = sorter.run(arg, it->getTerm());
        if (result) {
            arg->stack->tryAdd(make_shared<VarInfo>(it->getSymbol()->toString(), result, node));
        } else {
            return;
        }
    }

    TermSorter sorter;
    shared_ptr<Sort> result = sorter.run(arg, node->getTerm());
    if (result) {
        ret = result;
    } else {
        stringstream ss;
        ss << "Term '";
        string termstr = node->getTerm()->toString();
        if (termstr.length() > 50) {
            ss << string(termstr, 50) << "[...]";
        } else {
            ss << termstr;
        }
        ss << "' (" << node->getTerm()->getRowLeft() << ":" << node->getTerm()->getColLeft() << " - "
        << node->getTerm()->getRowRight() << ":" << node->getTerm()->getColRight()
        << ") is not well-sorted";
        arg->checker->addError(ss.str(), node);
    }

    arg->stack->pop();
}

void SortednessChecker::TermSorter::visit(std::shared_ptr<ForallTerm> node) {
    arg->stack->push();

    vector<shared_ptr<SortedVariable>> &bindings = node->getBindings();
    for (auto it : bindings) {
        arg->stack->tryAdd(make_shared<VarInfo>(it->getSymbol()->toString(),
                                                arg->stack->expand(it->getSort()), node));
    }

    TermSorter sorter;
    shared_ptr<Sort> result = sorter.run(arg, node->getTerm());
    string resstr = result->toString();
    if (result) {
        if (result->toString() == "Bool") {
            ret = result;
        } else {
            stringstream ss;
            ss << "Assertion term '";
            string termstr = node->getTerm()->toString();
            if (termstr.length() > 50) {
                ss << string(termstr, 50) << "[...]";
            } else {
                ss << termstr;
            }
            ss << "' (" << node->getTerm()->getRowLeft() << ":" << node->getTerm()->getColLeft() << " - "
            << node->getTerm()->getRowRight() << ":" << node->getTerm()->getColRight()
            << ") is of type " << resstr << ", not Bool";
            arg->checker->addError(ss.str(), node);
        }
    } else {
        stringstream ss;
        ss << "Term '";
        string termstr = node->getTerm()->toString();
        if (termstr.length() > 50) {
            ss << string(termstr, 50) << "[...]";
        } else {
            ss << termstr;
        }
        ss << "' (" << node->getTerm()->getRowLeft() << ":" << node->getTerm()->getColLeft() << " - "
        << node->getTerm()->getRowRight() << ":" << node->getTerm()->getColRight()
        << ") is not well-sorted";
        arg->checker->addError(ss.str(), node);
    }

    arg->stack->pop();
}

void SortednessChecker::TermSorter::visit(std::shared_ptr<ExistsTerm> node) {
    arg->stack->push();

    vector<shared_ptr<SortedVariable>> &bindings = node->getBindings();
    for (auto it : bindings) {
        arg->stack->tryAdd(make_shared<VarInfo>(it->getSymbol()->toString(),
                                                arg->stack->expand(it->getSort()), node));
    }

    TermSorter sorter;
    shared_ptr<Sort> result = sorter.run(arg, node->getTerm());
    string resstr = result->toString();
    if (result) {
        if (result->toString() == "Bool") {
            ret = result;
        } else {
            stringstream ss;
            ss << "Assertion term '";
            string termstr = node->getTerm()->toString();
            if (termstr.length() > 50) {
                ss << string(termstr, 50) << "[...]";
            } else {
                ss << termstr;
            }
            ss << "' (" << node->getTerm()->getRowLeft() << ":" << node->getTerm()->getColLeft() << " - "
            << node->getTerm()->getRowRight() << ":" << node->getTerm()->getColRight()
            << ") is of type " << resstr << ", not Bool";
            arg->checker->addError(ss.str(), node);
        }
    } else {
        stringstream ss;
        ss << "Term '";
        string termstr = node->getTerm()->toString();
        if (termstr.length() > 50) {
            ss << string(termstr, 50) << "[...]";
        } else {
            ss << termstr;
        }
        ss << "' (" << node->getTerm()->getRowLeft() << ":" << node->getTerm()->getColLeft() << " - "
        << node->getTerm()->getRowRight() << ":" << node->getTerm()->getColRight()
        << ") is not well-sorted";
        arg->checker->addError(ss.str(), node);
    }
    arg->stack->pop();
}

void SortednessChecker::TermSorter::visit(std::shared_ptr<AnnotatedTerm> node) {
    node->getTerm()->accept(this);
}