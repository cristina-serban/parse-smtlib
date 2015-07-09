#include "ast_sortedness_checker.h"
#include "ast_syntax_checker.h"
#include "../ast/ast_command.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_theory.h"
#include "../parser/smt_parser.h"
#include "../util/smt_logger.h"

#include <memory>
#include <sstream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

shared_ptr<SortednessChecker::SortednessCheckError>
SortednessChecker::addError(string message, shared_ptr<AstNode> node,
                            shared_ptr<SortednessChecker::SortednessCheckError> err) {
    if (!err) {
        shared_ptr<SortednessCheckErrorInfo> errInfo =
                make_shared<SortednessCheckErrorInfo>(message);
        err = make_shared<SortednessCheckError>(errInfo, node);
        errors[string(node->getFilename()->c_str())].push_back(err);
    } else {
        shared_ptr<SortednessCheckErrorInfo> errInfo =
                make_shared<SortednessCheckErrorInfo>(message);
        err->infos.push_back(errInfo);
    }

    return err;
}

shared_ptr<SortednessChecker::SortednessCheckError>
SortednessChecker::addError(string message, shared_ptr<AstNode> node,
                            shared_ptr<SymbolInfo> info,
                            shared_ptr<SortednessChecker::SortednessCheckError> err) {
    if (!err) {
        shared_ptr<SortednessCheckErrorInfo> errInfo =
                make_shared<SortednessCheckErrorInfo>(message, info);
        err = make_shared<SortednessCheckError>(errInfo, node);
        errors[string(node->getFilename()->c_str())].push_back(err);
    } else {
        shared_ptr<SortednessCheckErrorInfo> errInfo =
                make_shared<SortednessCheckErrorInfo>(message, info);
        err->infos.push_back(errInfo);
    }

    return err;
}

void SortednessChecker::addError(string message, shared_ptr<AstNode> node) {
    shared_ptr<SortednessCheckErrorInfo> errInfo =
            make_shared<SortednessCheckErrorInfo>(message);
    shared_ptr<SortednessCheckError> err =
            make_shared<SortednessCheckError>(errInfo, node);
    errors[string(node->getFilename()->c_str())].push_back(err);
}

void SortednessChecker::addError(string message, shared_ptr<AstNode> node,
                                 shared_ptr<SymbolInfo> info) {
    shared_ptr<SortednessCheckErrorInfo> errInfo =
            make_shared<SortednessCheckErrorInfo>(message, info);
    shared_ptr<SortednessCheckError> err =
            make_shared<SortednessCheckError>(errInfo, node);
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

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<SimpleFunDeclaration> node) {
    vector<shared_ptr<Sort>>& sig = node->getSignature();
    vector<shared_ptr<Sort>> newsig;

    for (vector<shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
        newsig.push_back(arg->expand(*it));
    }

    return make_shared<FunInfo>(node->getIdentifier()->toString(), newsig,
                                node->getAttributes(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<ParametricFunDeclaration> node) {
    vector<shared_ptr<Sort>>& sig = node->getSignature();
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
    vector<shared_ptr<Sort>>& sig = node->getParams();
    vector<shared_ptr<Sort>> newsig;

    for (vector<shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
        shared_ptr<Sort> itsort = arg->expand(*it);
        newsig.push_back(itsort);
    }
    shared_ptr<Sort> retsort = arg->expand(node->getSort());
    newsig.push_back(retsort);

    return make_shared<FunInfo>(node->getSymbol()->toString(), newsig, node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<DefineFunCommand> node) {
    vector<shared_ptr<Sort>> newsig;
    vector<shared_ptr<SortedVariable>>& params = node->getDefinition()->getSignature()->getParams();
    for (vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        newsig.push_back(arg->expand((*it)->getSort()));
    }
    newsig.push_back(arg->expand(node->getDefinition()->getSignature()->getSort()));

    return make_shared<FunInfo>(node->getDefinition()->getSignature()->getSymbol()->toString(),
                                newsig, node->getDefinition()->getBody(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<DefineFunRecCommand> node) {
    vector<shared_ptr<Sort>> newsig;
    vector<shared_ptr<SortedVariable>>& params = node->getDefinition()->getSignature()->getParams();
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
        vector<shared_ptr<SortedVariable>>& params = node->getDeclarations()[i]->getParams();
        for (vector<shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
            newsig.push_back(arg->expand((*it)->getSort()));
        }
        newsig.push_back(arg->expand(node->getDeclarations()[i]->getSort()));

        infos.push_back(make_shared<FunInfo>(node->getDeclarations()[i]->getSymbol()->toString(),
                                             newsig, node->getBodies()[i], node));
    }

    return infos;
}

vector<shared_ptr<SymbolInfo>> SortednessChecker::getInfo(shared_ptr<DeclareDatatypeCommand> node) {
    vector<shared_ptr<SymbolInfo>> infos;
    string typeName = node->getSymbol()->toString();

    shared_ptr<ParametricDatatypeDeclaration> pdecl =
            dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->getDeclaration());

    if (pdecl) {
        // Add datatype (parametric) sort info
        infos.push_back(make_shared<SortInfo>(typeName, pdecl->getParams().size(), node));

        // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
        shared_ptr<Sort> typeSort = make_shared<Sort>(make_shared<SimpleIdentifier>(node->getSymbol()));
        for (vector<shared_ptr<Symbol>>::iterator it = pdecl->getParams().begin();
             it != pdecl->getParams().end(); it++) {
            typeSort->getArgs().push_back(make_shared<Sort>(make_shared<SimpleIdentifier>(*it)));
        }
        typeSort = arg->expand(typeSort);

        for (vector<shared_ptr<ConstructorDeclaration>>::iterator consit = pdecl->getConstructors().begin();
             consit != pdecl->getConstructors().end(); consit++) {
            // Start building function info for current constructor
            string consName = (*consit)->getSymbol()->toString();
            vector<shared_ptr<Sort>> consSig;
            for (vector<shared_ptr<SelectorDeclaration>>::iterator selit = (*consit)->getSelectors().begin();
                 selit != (*consit)->getSelectors().end(); selit++) {
                // Add sort of current selector to current constructor signature
                consSig.push_back(arg->expand((*selit)->getSort()));

                // Build function info for current selector
                string selName = (*selit)->getSymbol()->toString();
                vector<shared_ptr<Sort>> selSig;
                selSig.push_back(typeSort);
                selSig.push_back(arg->expand((*selit)->getSort()));

                // Add selector function info
                infos.push_back(make_shared<FunInfo>(selName, selSig, pdecl->getParams(), node));
            }

            // Add constructor function info
            infos.push_back(make_shared<FunInfo>(consName, consSig, pdecl->getParams(), node));
        }

    } else {
        // Add datatype (non-parametric) sort info
        infos.push_back(make_shared<SortInfo>(typeName, 0, node));

        // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
        shared_ptr<Sort> typeSort = make_shared<Sort>(make_shared<SimpleIdentifier>(node->getSymbol()));
        typeSort = arg->expand(typeSort);

        shared_ptr<SimpleDatatypeDeclaration> sdecl =
                dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->getDeclaration());

        for (vector<shared_ptr<ConstructorDeclaration>>::iterator consit = sdecl->getConstructors().begin();
             consit != sdecl->getConstructors().end(); consit++) {
            // Start building function info for current constructor
            string consName = (*consit)->getSymbol()->toString();
            vector<shared_ptr<Sort>> consSig;
            for (vector<shared_ptr<SelectorDeclaration>>::iterator selit = (*consit)->getSelectors().begin();
                 selit != (*consit)->getSelectors().end(); selit++) {
                // Add sort of current selector to current constructor signature
                consSig.push_back(arg->expand((*selit)->getSort()));

                // Build function info for current selector
                string selName = (*selit)->getSymbol()->toString();
                vector<shared_ptr<Sort>> selSig;
                selSig.push_back(typeSort);
                selSig.push_back(arg->expand((*selit)->getSort()));

                // Add selector function info
                infos.push_back(make_shared<FunInfo>(selName, selSig, node));
            }

            // Add constructor function info
            infos.push_back(make_shared<FunInfo>(consName, consSig, node));
        }
    }

    return infos;
}

vector<shared_ptr<SymbolInfo>> SortednessChecker::getInfo(shared_ptr<DeclareDatatypesCommand> node) {
    vector<shared_ptr<SymbolInfo>> infos;

    for (vector<shared_ptr<SortDeclaration>>::iterator it = node->getSorts().begin();
         it != node->getSorts().end(); it++) {
        string typeName = (*it)->getSymbol()->toString();
        unsigned long arity = (unsigned long) (*it)->getArity()->getValue();

        // Add datatype sort info
        infos.push_back(make_shared<SortInfo>(typeName, 0, node));
    }

    for (unsigned long i = 0; i < node->getSorts().size(); i++) {
        shared_ptr<ParametricDatatypeDeclaration> pdecl =
                dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->getDeclarations()[i]);
        if (pdecl) {
            // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
            shared_ptr<Sort> typeSort =
                    make_shared<Sort>(make_shared<SimpleIdentifier>(node->getSorts()[i]->getSymbol()));
            typeSort = arg->expand(typeSort);

            for (vector<shared_ptr<Symbol>>::iterator it = pdecl->getParams().begin();
                 it != pdecl->getParams().end(); it++) {
                typeSort->getArgs().push_back(make_shared<Sort>(make_shared<SimpleIdentifier>(*it)));
            }

            for (vector<shared_ptr<ConstructorDeclaration>>::iterator consit = pdecl->getConstructors().begin();
                 consit != pdecl->getConstructors().end(); consit++) {
                // Start building function info for current constructor
                string consName = (*consit)->getSymbol()->toString();
                vector<shared_ptr<Sort>> consSig;
                for (vector<shared_ptr<SelectorDeclaration>>::iterator selit = (*consit)->getSelectors().begin();
                     selit != (*consit)->getSelectors().end(); selit++) {
                    // Add sort of current selector to current constructor signature
                    consSig.push_back(arg->expand((*selit)->getSort()));

                    // Build function info for current selector
                    string selName = (*selit)->getSymbol()->toString();
                    vector<shared_ptr<Sort>> selSig;
                    selSig.push_back(typeSort);
                    selSig.push_back(arg->expand((*selit)->getSort()));

                    // Add selector function info
                    infos.push_back(make_shared<FunInfo>(selName, selSig, pdecl->getParams(), node));
                }

                // Add constructor function info
                infos.push_back(make_shared<FunInfo>(consName, consSig, pdecl->getParams(), node));
            }
        } else {
            // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
            shared_ptr<Sort> typeSort =
                    make_shared<Sort>(make_shared<SimpleIdentifier>(node->getSorts()[i]->getSymbol()));
            typeSort = arg->expand(typeSort);

            shared_ptr<SimpleDatatypeDeclaration> sdecl =
                    dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->getDeclarations()[i]);

            for (vector<shared_ptr<ConstructorDeclaration>>::iterator consit = sdecl->getConstructors().begin();
                 consit != sdecl->getConstructors().end(); consit++) {
                // Start building function info for current constructor
                string consName = (*consit)->getSymbol()->toString();
                vector<shared_ptr<Sort>> consSig;
                for (vector<shared_ptr<SelectorDeclaration>>::iterator selit = (*consit)->getSelectors().begin();
                     selit != (*consit)->getSelectors().end(); selit++) {
                    // Add sort of current selector to current constructor signature
                    consSig.push_back(arg->expand((*selit)->getSort()));

                    // Build function info for current selector
                    string selName = (*selit)->getSymbol()->toString();
                    vector<shared_ptr<Sort>> selSig;
                    selSig.push_back(typeSort);
                    selSig.push_back(arg->expand((*selit)->getSort()));

                    // Add selector function info
                    infos.push_back(make_shared<FunInfo>(selName, selSig, node));
                }

                // Add constructor function info
                infos.push_back(make_shared<FunInfo>(consName, consSig, node));
            }
        }
    }

    return infos;
}

void SortednessChecker::loadTheory(string theory,
                                   std::shared_ptr<AstNode> node,
                                   std::shared_ptr<SortednessCheckError> err) {
    Parser* parser = new Parser;
    string path = "input/Theories/" + theory + ".smt2";

    FILE* f = fopen(path.c_str(), "r");
    if(f) {
        fclose(f);
        shared_ptr<AstNode> ast = parser->parse(path);
        if(ast) {
            ast->accept(this);
        } else {
            ret = false;
            addError("Cannot load theory " + theory, node, err);
        }
    } else {
        ret = false;
        addError("Unknown theory '" + theory + "'", node, err);
    }
}

void SortednessChecker::loadLogic(string logic,
                                  std::shared_ptr<AstNode> node,
                                  std::shared_ptr<SortednessCheckError> err) {
    Parser* parser = new Parser;
    string path = "input/Logics/" + logic + ".smt2";

    FILE* f = fopen(path.c_str(), "r");
    if(f) {
        fclose(f);
        shared_ptr<AstNode> ast = parser->parse(path);
        if(ast) {
            ast->accept(this);
        } else {
            addError("Cannot set logic to " + logic, node, err);
        }
    } else {
        addError("Unknown logic " + logic, node, err);
    }
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
SortednessChecker::checkSort(vector<shared_ptr<Symbol>>& params,
                             shared_ptr<Sort> sort,
                             shared_ptr<AstNode> source,
                             shared_ptr<SortednessChecker::SortednessCheckError> err) {
    string name = sort->getIdentifier()->toString();
    bool isParam = false;
    for (vector<shared_ptr<Symbol>>::iterator it = params.begin(); it != params.end(); it++) {
        if (name == (*it)->toString())
            isParam = true;
    }

    if (!isParam) {
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
                    checkSort(params, *it, source, err);
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
                ss << string(termstr, 0, 50) << "[...]";
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
            ss << string(termstr, 0, 50) << "[...]";
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
        addError("Constant '" + nodeInfo->name + "' already exists with same sort", node, dupInfo, err);
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

    if (dupInfo) {
        ret = false;
        addError("Function '" + nodeInfo->name + "' already exists with the same signature", node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<DeclareDatatypeCommand> node) {
    shared_ptr<SortednessCheckError> err;

    shared_ptr<ParametricDatatypeDeclaration> pdecl =
            dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->getDeclaration());

    if (pdecl) {
        for (vector<shared_ptr<ConstructorDeclaration>>::iterator consit = pdecl->getConstructors().begin();
             consit != pdecl->getConstructors().end(); consit++) {
            for (vector<shared_ptr<SelectorDeclaration>>::iterator selit = (*consit)->getSelectors().begin();
                 selit != (*consit)->getSelectors().end(); selit++) {
                err = checkSort(pdecl->getParams(), (*selit)->getSort(), node, err);
            }
        }
    } else {
        shared_ptr<SimpleDatatypeDeclaration> sdecl =
                dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->getDeclaration());

        for (vector<shared_ptr<ConstructorDeclaration>>::iterator consit = sdecl->getConstructors().begin();
             consit != sdecl->getConstructors().end(); consit++) {
            for (vector<shared_ptr<SelectorDeclaration>>::iterator selit = (*consit)->getSelectors().begin();
                 selit != (*consit)->getSelectors().end(); selit++) {
                err = checkSort((*selit)->getSort(), node, err);
            }
        }
    }

    vector<shared_ptr<SymbolInfo>> infos = getInfo(node);
    for (vector<shared_ptr<SymbolInfo>>::iterator it = infos.begin(); it != infos.end(); it++) {
        shared_ptr<FunInfo> funInfo = dynamic_pointer_cast<FunInfo>(*it);
        if (funInfo) {
            shared_ptr<FunInfo> dupInfo = arg->tryAdd(funInfo);

            if (dupInfo) {
                ret = false;
                err = addError("Function '" + funInfo->name + "' already exists with the same signature", node, dupInfo,
                               err);
            }

        } else {
            shared_ptr<SortInfo> sortInfo = dynamic_pointer_cast<SortInfo>(*it);
            shared_ptr<SortInfo> dupInfo = arg->tryAdd(sortInfo);

            if (dupInfo) {
                ret = false;
                err = addError("Sort symbol '" + sortInfo->name + "' already exists", node, dupInfo, err);
            }
        }
    }
}

void SortednessChecker::visit(shared_ptr<DeclareDatatypesCommand> node) {
    shared_ptr<SortednessCheckError> err;

    vector<shared_ptr<SymbolInfo>> infos = getInfo(node);

    for (vector<shared_ptr<SymbolInfo>>::iterator it = infos.begin(); it != infos.end(); it++) {
        shared_ptr<SymbolInfo> symbolInfo = *it;
        shared_ptr<SortInfo> sortInfo = dynamic_pointer_cast<SortInfo>((*it));
        if (sortInfo) {
            shared_ptr<SortInfo> dupInfo = arg->tryAdd(sortInfo);
            if (dupInfo) {
                ret = false;
                err = addError("Sort symbol '" + sortInfo->name + "' already exists", node, dupInfo, err);
            }
        }
    }

    for (unsigned long i = 0; i < node->getSorts().size(); i++) {
        shared_ptr<SortednessCheckError> declerr;

        shared_ptr<ParametricDatatypeDeclaration> pdecl =
                dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->getDeclarations()[i]);

        if (pdecl) {
            for (vector<shared_ptr<ConstructorDeclaration>>::iterator consit = pdecl->getConstructors().begin();
                 consit != pdecl->getConstructors().end(); consit++) {
                for (vector<shared_ptr<SelectorDeclaration>>::iterator selit = (*consit)->getSelectors().begin();
                     selit != (*consit)->getSelectors().end(); selit++) {
                    declerr = checkSort(pdecl->getParams(), (*selit)->getSort(), pdecl, declerr);
                }
            }
        } else {
            shared_ptr<SimpleDatatypeDeclaration> sdecl =
                    dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->getDeclarations()[i]);

            for (vector<shared_ptr<ConstructorDeclaration>>::iterator consit = sdecl->getConstructors().begin();
                 consit != sdecl->getConstructors().end(); consit++) {
                for (vector<shared_ptr<SelectorDeclaration>>::iterator selit = (*consit)->getSelectors().begin();
                     selit != (*consit)->getSelectors().end(); selit++) {
                    declerr = checkSort((*selit)->getSort(), sdecl, declerr);
                }
            }
        }

        for (vector<shared_ptr<SymbolInfo>>::iterator it = infos.begin(); it != infos.end(); it++) {
            shared_ptr<SymbolInfo> symbolInfo = *it;
            shared_ptr<FunInfo> funInfo = dynamic_pointer_cast<FunInfo>(symbolInfo);
            if (funInfo) {
                shared_ptr<FunInfo> dupInfo = arg->tryAdd(funInfo);

                if (dupInfo) {
                    ret = false;
                    err = addError("Function '" + funInfo->name + "' already exists with the same signature", node,
                                   dupInfo, err);
                }
            }
        }
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

        vector<shared_ptr<SortedVariable>>& bindings = node->getDefinition()->getSignature()->getParams();
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
                    ss << string(termstr, 0, 50) << "[...]";
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
                ss << string(termstr, 0, 50) << "[...]";
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

        vector<shared_ptr<SortedVariable>>& bindings = node->getDefinition()->getSignature()->getParams();
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
                    ss << string(termstr, 0, 50) << "[...]";
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
                ss << string(termstr, 0, 50) << "[...]";
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

void SortednessChecker::visit(shared_ptr<DefineFunsRecCommand> node) {
    shared_ptr<SortednessCheckError> err;
    vector<shared_ptr<FunctionDeclaration>>& decls = node->getDeclarations();
    vector<shared_ptr<Term>>& bodies = node->getBodies();

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
            vector<shared_ptr<SortedVariable>>& bindings = decls[i]->getParams();
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
                        ss << string(termstr, 0, 50) << "[...]";
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
                    ss << string(termstr, 0, 50) << "[...]";
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
    err = checkSort(node->getParams(), node->getSort(), node, err);

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
                ss << string(termstr, 0, 50) << "[...]";
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
    currentLogic = "";
    currentTheories.clear();
}

void SortednessChecker::visit(shared_ptr<SetLogicCommand> node) {
    shared_ptr<SortednessCheckError> err;
    if(currentLogic != "") {
        ret = false;
        addError("Logic already set to '" + currentLogic + "'", node);
    } else {
        currentLogic = node->getLogic()->toString();
        loadLogic(currentLogic, node, err);
    }
}

void SortednessChecker::visit(shared_ptr<Logic> node) {
    vector<shared_ptr<Attribute>> attrs = node->getAttributes();
    for (vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;
        if (attr->getKeyword()->getValue() == ":theories") {
            shared_ptr<SortednessCheckError> err;

            CompAttributeValue* val = dynamic_cast<CompAttributeValue*>(attr->getValue().get());
            for (vector<shared_ptr<AttributeValue>>::iterator v = val->getValues().begin();
                 v != val->getValues().end(); v++) {
                string theory = dynamic_cast<Symbol*>((*v).get())->toString();
                if(currentTheories.find(theory) != currentTheories.end()) {
                    ret = false;
                    err = addError("Theory '" + theory + "' already loaded", attr, err);
                } else {
                    currentTheories[theory] = true;
                    loadTheory(theory, attr, err);
                }
            }
        }
    }
}

void SortednessChecker::visit(shared_ptr<Theory> node) {
    vector<shared_ptr<Attribute>> attrs = node->getAttributes();
    for (vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;

        if (attr->getKeyword()->getValue() == ":sorts" || attr->getKeyword()->getValue() == ":funs") {
            CompAttributeValue* val = dynamic_cast<CompAttributeValue*>(attr->getValue().get());
            for (vector<shared_ptr<AttributeValue>>::iterator v = val->getValues().begin();
                 v != val->getValues().end(); v++) {
                (*v)->accept(this);
            }
        }
    }
}

void SortednessChecker::visit(shared_ptr<Script> node) {
    vector<shared_ptr<Command>>& commands = node->getCommands();
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
        err = addError("Sort for meta specification constant '" +
                 nodeInfo->name + "' already declared", node, dupInfo[0], err);
    } else {
        arg->tryAdd(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<SimpleFunDeclaration> node) {
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

    vector<shared_ptr<Sort>> sig = node->getSignature();
    for (vector<shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
        err = checkSort(node->getParams(), *it, node, err);
    }

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
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
            if(err->node) {
                ss << err->node->getRowLeft() << ":" << err->node->getColLeft()
                << " - " << err->node->getRowRight() << ":" << err->node->getColRight() << "   ";

                string nodestr = err->node->toString();
                if (nodestr.length() > 100)
                    ss << string(nodestr, 0, 100) << "[...]";
                else
                    ss << nodestr;

                ss << endl;
            }

            for (vector<shared_ptr<SortednessCheckErrorInfo>>::iterator info = err->infos.begin();
                 info != err->infos.end(); info++) {
                shared_ptr<AstNode> source;

                if ((*info)->info) {
                    source = (*info)->info->source;
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
                        ss << string(sourcestr, 0, 100);
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