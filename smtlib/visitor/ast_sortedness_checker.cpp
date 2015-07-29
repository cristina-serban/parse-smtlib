#include "ast_sortedness_checker.h"
#include "ast_syntax_checker.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_theory.h"
#include "../parser/smt_parser.h"
#include "../util/global_settings.h"
#include "../util/error_messages.h"
#include "../smt_execution.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

/* ============================= SortednessCheckerContext ============================= */

SortednessCheckerContext::SortednessCheckerContext() {
    stack = make_shared<SymbolStack>();
}

SortednessCheckerContext::SortednessCheckerContext(shared_ptr<SymbolStack> stack)
        : stack(stack) { }

shared_ptr<SymbolStack> SortednessCheckerContext::getStack() {
    return stack;
}

vector<string>& SortednessCheckerContext::getCurrentTheories() {
    return currentTheories;
}

string SortednessCheckerContext::getCurrentLogic() {
    return currentLogic;
}

void SortednessCheckerContext::setCurrentLogic(string logic) {
    currentLogic = logic;
}

/* ================================ SortednessChecker ================================= */

shared_ptr<SortednessChecker::NodeError>
SortednessChecker::addError(string message, shared_ptr<AstNode> node,
                            shared_ptr<SortednessChecker::NodeError> err) {
    if (!err) {
        shared_ptr<Error> errInfo =
                make_shared<Error>(message);
        err = make_shared<NodeError>(errInfo, node);
        if (node && node->getFilename())
            errors[string(node->getFilename()->c_str())].push_back(err);
        else
            errors[""].push_back(err);
    } else {
        shared_ptr<Error> errInfo =
                make_shared<Error>(message);
        err->errs.push_back(errInfo);
    }

    return err;
}

shared_ptr<SortednessChecker::NodeError>
SortednessChecker::addError(string message, shared_ptr<AstNode> node,
                            shared_ptr<SymbolInfo> info,
                            shared_ptr<SortednessChecker::NodeError> err) {
    if (!err) {
        shared_ptr<Error> errInfo =
                make_shared<Error>(message, info);
        err = make_shared<NodeError>(errInfo, node);
        if (node && node->getFilename())
            errors[string(node->getFilename()->c_str())].push_back(err);
        else
            errors[""].push_back(err);
    } else {
        shared_ptr<Error> errInfo =
                make_shared<Error>(message, info);
        err->errs.push_back(errInfo);
    }

    return err;
}

void SortednessChecker::addError(string message, shared_ptr<AstNode> node) {
    shared_ptr<Error> errInfo =
            make_shared<Error>(message);
    shared_ptr<NodeError> err =
            make_shared<NodeError>(errInfo, node);
    if (node && node->getFilename())
        errors[string(node->getFilename()->c_str())].push_back(err);
    else
        errors[""].push_back(err);
}

void SortednessChecker::addError(string message, shared_ptr<AstNode> node,
                                 shared_ptr<SymbolInfo> info) {
    shared_ptr<Error> errInfo =
            make_shared<Error>(message, info);
    shared_ptr<NodeError> err =
            make_shared<NodeError>(errInfo, node);
    errors[string(node->getFilename()->c_str())].push_back(err);
}

shared_ptr<SortInfo> SortednessChecker::getInfo(shared_ptr<DeclareSortCommand> node) {
    return make_shared<SortInfo>(node->getSymbol()->toString(), node->getArity()->getValue(), node);
}

shared_ptr<SortInfo> SortednessChecker::getInfo(shared_ptr<DefineSortCommand> node) {
    return make_shared<SortInfo>(node->getSymbol()->toString(), node->getParams().size(),
                                 node->getParams(), ctx->getStack()->expand(node->getSort()), node);
}


shared_ptr<SortInfo> SortednessChecker::getInfo(shared_ptr<SortSymbolDeclaration> node) {
    return make_shared<SortInfo>(node->getIdentifier()->toString(),
                                 node->getArity()->getValue(),
                                 node->getAttributes(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<SpecConstFunDeclaration> node) {
    vector<shared_ptr<Sort>> sig;
    sig.push_back(ctx->getStack()->expand(node->getSort()));

    return make_shared<FunInfo>(node->getConstant()->toString(), sig, node->getAttributes(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<MetaSpecConstFunDeclaration> node) {
    vector<shared_ptr<Sort>> sig;
    sig.push_back(ctx->getStack()->expand(node->getSort()));
    return make_shared<FunInfo>(node->getConstant()->toString(), sig, node->getAttributes(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<SimpleFunDeclaration> node) {
    vector<shared_ptr<Sort>> &sig = node->getSignature();
    vector<shared_ptr<Sort>> newsig;

    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        newsig.push_back(ctx->getStack()->expand(*sortIt));
    }

    shared_ptr<FunInfo> funInfo = make_shared<FunInfo>(node->getIdentifier()->toString(), newsig,
                                                       node->getAttributes(), node);

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();
    for (auto attr = attrs.begin(); attr != attrs.end(); attr++) {
        if ((*attr)->toString() == KW_RIGHT_ASSOC) {
            funInfo->assocR = true;
        }

        if ((*attr)->toString() == KW_LEFT_ASSOC) {
            funInfo->assocL = true;
        }

        if ((*attr)->toString() == KW_CHAINABLE) {
            funInfo->chainable = true;
        }

        if ((*attr)->toString() == KW_PAIRWISE) {
            funInfo->pairwise = true;
        }
    }

    return funInfo;
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<ParametricFunDeclaration> node) {
    vector<shared_ptr<Sort>> &sig = node->getSignature();
    vector<shared_ptr<Sort>> newsig;

    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        newsig.push_back(ctx->getStack()->expand(*sortIt));
    }

    shared_ptr<FunInfo> funInfo = make_shared<FunInfo>(node->getIdentifier()->toString(), newsig,
                                                       node->getParams(), node->getAttributes(), node);

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();
    for (auto attr = attrs.begin(); attr != attrs.end(); attr++) {
        if ((*attr)->toString() == KW_RIGHT_ASSOC) {
            funInfo->assocR = true;
        }

        if ((*attr)->toString() == KW_LEFT_ASSOC) {
            funInfo->assocL = true;
        }

        if ((*attr)->toString() == KW_CHAINABLE) {
            funInfo->chainable = true;
        }

        if ((*attr)->toString() == KW_PAIRWISE) {
            funInfo->pairwise = true;
        }
    }

    return funInfo;
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<DeclareConstCommand> node) {
    vector<shared_ptr<Sort>> sig;
    sig.push_back(ctx->getStack()->expand(node->getSort()));

    return make_shared<FunInfo>(node->getSymbol()->toString(), sig, node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<DeclareFunCommand> node) {
    vector<shared_ptr<Sort>> &sig = node->getParams();
    vector<shared_ptr<Sort>> newsig;

    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        shared_ptr<Sort> itsort = ctx->getStack()->expand(*sortIt);
        newsig.push_back(itsort);
    }
    shared_ptr<Sort> retsort = ctx->getStack()->expand(node->getSort());
    newsig.push_back(retsort);

    return make_shared<FunInfo>(node->getSymbol()->toString(), newsig, node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<DefineFunCommand> node) {
    vector<shared_ptr<Sort>> newsig;
    vector<shared_ptr<SortedVariable>> &params = node->getDefinition()->getSignature()->getParams();
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        newsig.push_back(ctx->getStack()->expand((*paramIt)->getSort()));
    }
    newsig.push_back(ctx->getStack()->expand(node->getDefinition()->getSignature()->getSort()));

    return make_shared<FunInfo>(node->getDefinition()->getSignature()->getSymbol()->toString(),
                                newsig, node->getDefinition()->getBody(), node);
}

shared_ptr<FunInfo> SortednessChecker::getInfo(shared_ptr<DefineFunRecCommand> node) {
    vector<shared_ptr<Sort>> newsig;
    vector<shared_ptr<SortedVariable>> &params = node->getDefinition()->getSignature()->getParams();
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        newsig.push_back(ctx->getStack()->expand((*paramIt)->getSort()));
    }
    newsig.push_back(ctx->getStack()->expand(node->getDefinition()->getSignature()->getSort()));

    return make_shared<FunInfo>(node->getDefinition()->getSignature()->getSymbol()->toString(),
                                newsig, node->getDefinition()->getBody(), node);
}

vector<shared_ptr<FunInfo>> SortednessChecker::getInfo(shared_ptr<DefineFunsRecCommand> node) {
    vector<shared_ptr<FunInfo>> infos;
    for (unsigned long i = 0; i < node->getDeclarations().size(); i++) {
        vector<shared_ptr<Sort>> newsig;
        vector<shared_ptr<SortedVariable>> &params = node->getDeclarations()[i]->getParams();
        for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
            newsig.push_back(ctx->getStack()->expand((*paramIt)->getSort()));
        }
        newsig.push_back(ctx->getStack()->expand(node->getDeclarations()[i]->getSort()));

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

        vector<shared_ptr<Symbol>> params = pdecl->getParams();
        for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
            typeSort->getArgs().push_back(make_shared<Sort>(make_shared<SimpleIdentifier>(*paramIt)));
        }

        typeSort = ctx->getStack()->expand(typeSort);

        vector<shared_ptr<ConstructorDeclaration>> constructors = pdecl->getConstructors();
        for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
            // Start building function info for current constructor
            string consName = (*consIt)->getSymbol()->toString();
            vector<shared_ptr<Sort>> consSig;

            vector<shared_ptr<SelectorDeclaration>> selectors = (*consIt)->getSelectors();
            for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                // Add sort of current selector to current constructor signature
                consSig.push_back(ctx->getStack()->expand((*selIt)->getSort()));

                // Build function info for current selector
                string selName = (*selIt)->getSymbol()->toString();
                vector<shared_ptr<Sort>> selSig;
                selSig.push_back(typeSort);
                selSig.push_back(ctx->getStack()->expand((*selIt)->getSort()));

                // Add selector function info
                infos.push_back(make_shared<FunInfo>(selName, selSig, pdecl->getParams(), node));
            }

            // Add constructor function info
            consSig.push_back(typeSort);
            infos.push_back(make_shared<FunInfo>(consName, consSig, pdecl->getParams(), node));
        }

    } else {
        // Add datatype (non-parametric) sort info
        infos.push_back(make_shared<SortInfo>(typeName, 0, node));

        // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
        shared_ptr<Sort> typeSort = make_shared<Sort>(make_shared<SimpleIdentifier>(node->getSymbol()));
        typeSort = ctx->getStack()->expand(typeSort);

        shared_ptr<SimpleDatatypeDeclaration> sdecl =
                dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->getDeclaration());

        vector<shared_ptr<ConstructorDeclaration>> constructors = sdecl->getConstructors();

        for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
            // Start building function info for current constructor
            string consName = (*consIt)->getSymbol()->toString();
            vector<shared_ptr<Sort>> consSig;
            vector<shared_ptr<SelectorDeclaration>> selectors = (*consIt)->getSelectors();

            for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                // Add sort of current selector to current constructor signature
                consSig.push_back(ctx->getStack()->expand((*selIt)->getSort()));

                // Build function info for current selector
                string selName = (*selIt)->getSymbol()->toString();
                vector<shared_ptr<Sort>> selSig;
                selSig.push_back(typeSort);
                selSig.push_back(ctx->getStack()->expand((*selIt)->getSort()));

                // Add selector function info
                infos.push_back(make_shared<FunInfo>(selName, selSig, node));
            }

            // Add constructor function info
            consSig.push_back(typeSort);
            infos.push_back(make_shared<FunInfo>(consName, consSig, node));
        }
    }

    return infos;
}

vector<shared_ptr<SymbolInfo>> SortednessChecker::getInfo(shared_ptr<DeclareDatatypesCommand> node) {
    vector<shared_ptr<SymbolInfo>> infos;

    vector<shared_ptr<SortDeclaration>> datatypeSorts = node->getSorts();
    for (auto sortIt = datatypeSorts.begin(); sortIt != datatypeSorts.end(); sortIt++) {
        string typeName = (*sortIt)->getSymbol()->toString();
        unsigned long arity = (unsigned long) (*sortIt)->getArity()->getValue();

        // Add datatype sort info
        infos.push_back(make_shared<SortInfo>(typeName, arity, node));
    }

    for (unsigned long i = 0; i < node->getSorts().size(); i++) {
        shared_ptr<ParametricDatatypeDeclaration> pdecl =
                dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->getDeclarations()[i]);
        if (pdecl) {
            // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
            shared_ptr<Sort> typeSort =
                    make_shared<Sort>(make_shared<SimpleIdentifier>(node->getSorts()[i]->getSymbol()));
            typeSort = ctx->getStack()->expand(typeSort);

            vector<shared_ptr<Symbol>> params = pdecl->getParams();
            for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
                typeSort->getArgs().push_back(make_shared<Sort>(make_shared<SimpleIdentifier>(*paramIt)));
            }

            vector<shared_ptr<ConstructorDeclaration>> constructors = pdecl->getConstructors();

            for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
                // Start building function info for current constructor
                string consName = (*consIt)->getSymbol()->toString();
                vector<shared_ptr<Sort>> consSig;
                vector<shared_ptr<SelectorDeclaration>> selectors = (*consIt)->getSelectors();

                for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                    // Add sort of current selector to current constructor signature
                    consSig.push_back(ctx->getStack()->expand((*selIt)->getSort()));

                    // Build function info for current selector
                    string selName = (*selIt)->getSymbol()->toString();
                    vector<shared_ptr<Sort>> selSig;
                    selSig.push_back(typeSort);
                    selSig.push_back(ctx->getStack()->expand((*selIt)->getSort()));

                    // Add selector function info
                    infos.push_back(make_shared<FunInfo>(selName, selSig, pdecl->getParams(), node));
                }

                // Add constructor function info
                consSig.push_back(typeSort);
                infos.push_back(make_shared<FunInfo>(consName, consSig, pdecl->getParams(), node));
            }
        } else {
            // Build a sort representing the datatype (to be used in the signatures of the constructors and selectors)
            shared_ptr<Sort> typeSort =
                    make_shared<Sort>(make_shared<SimpleIdentifier>(node->getSorts()[i]->getSymbol()));
            typeSort = ctx->getStack()->expand(typeSort);

            shared_ptr<SimpleDatatypeDeclaration> sdecl =
                    dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->getDeclarations()[i]);

            vector<shared_ptr<ConstructorDeclaration>> constructors = sdecl->getConstructors();

            for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
                // Start building function info for current constructor
                string consName = (*consIt)->getSymbol()->toString();
                vector<shared_ptr<Sort>> consSig;

                vector<shared_ptr<SelectorDeclaration>> selectors = (*consIt)->getSelectors();

                for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                    // Add sort of current selector to current constructor signature
                    consSig.push_back(ctx->getStack()->expand((*selIt)->getSort()));

                    // Build function info for current selector
                    string selName = (*selIt)->getSymbol()->toString();
                    vector<shared_ptr<Sort>> selSig;
                    selSig.push_back(typeSort);
                    selSig.push_back(ctx->getStack()->expand((*selIt)->getSort()));

                    // Add selector function info
                    infos.push_back(make_shared<FunInfo>(selName, selSig, node));
                }

                // Add constructor function info
                consSig.push_back(typeSort);
                infos.push_back(make_shared<FunInfo>(consName, consSig, node));
            }
        }
    }

    return infos;
}

void SortednessChecker::loadTheory(string theory) {
    shared_ptr<AstNode> node;
    shared_ptr<NodeError> err;
    loadTheory(theory, node, err);
}

void SortednessChecker::loadTheory(string theory,
                                   shared_ptr<AstNode> node,
                                   shared_ptr<NodeError> err) {
    string path = LOC_THEORIES + theory + FILE_EXT_THEORY;
    FILE *f = fopen(path.c_str(), "r");
    if (f) {
        fclose(f);

        shared_ptr<SmtExecutionSettings> settings = make_shared<SmtExecutionSettings>();
        settings->setInputFromFile(path);
        settings->setCoreTheoryEnabled(false);
        settings->setSortCheckContext(ctx);

        SmtExecution exec(settings);
        if(exec.parse()) {
            if(exec.checkSortedness()) {
                //currentTheories[theory] = true;
            }
        } else {
            addError(ErrorMessages::buildTheoryUnloadable(theory), node, err);
        }
    } else {
        addError(ErrorMessages::buildTheoryUnknown(theory), node, err);
    }
}

void SortednessChecker::loadLogic(string logic,
                                  shared_ptr<AstNode> node,
                                  shared_ptr<NodeError> err) {
    string path = LOC_LOGICS + logic + FILE_EXT_LOGIC;
    FILE *f = fopen(path.c_str(), "r");
    if (f) {
        fclose(f);

        shared_ptr<SmtExecutionSettings> settings = make_shared<SmtExecutionSettings>();
        settings->setInputFromFile(path);
        settings->setCoreTheoryEnabled(false);
        settings->setSortCheckContext(ctx);

        SmtExecution exec(settings);
        if(exec.parse()) {
            exec.checkSortedness();
        } else {
            addError(ErrorMessages::buildLogicUnloadable(logic), node, err);
        }
    } else {
        addError(ErrorMessages::buildLogicUnknown(logic), node, err);
    }
}

shared_ptr<SortednessChecker::NodeError>
SortednessChecker::checkSort(shared_ptr<Sort> sort,
                             shared_ptr<AstNode> source,
                             shared_ptr<SortednessChecker::NodeError> err) {
    string name = sort->getIdentifier()->toString();
    shared_ptr<SortInfo> info = ctx->getStack()->getSortInfo(name);
    if (!info) {
        err = addError(ErrorMessages::buildSortUnknown(name, sort->getRowLeft(), sort->getColLeft(),
                                                       sort->getRowRight(), sort->getColRight()), source, err);

        vector<shared_ptr<Sort>> argSorts = sort->getArgs();
        for (auto sortIt = argSorts.begin(); sortIt != argSorts.end(); sortIt++) {
            checkSort(*sortIt, source, err);
        }
    } else {
        if (sort->getArgs().size() != info->arity) {
            err = addError(ErrorMessages::buildSortArity(name, info->arity, sort->getArgs().size(),
                                                         sort->getRowLeft(), sort->getColLeft(),
                                                         sort->getRowRight(), sort->getColRight()),
                           source, info, err);
        } else {
            vector<shared_ptr<Sort>> argSorts = sort->getArgs();
            for (auto sortIt = argSorts.begin(); sortIt != argSorts.end(); sortIt++) {
                checkSort(*sortIt, source, err);
            }
        }
    }
    return err;
}

shared_ptr<SortednessChecker::NodeError>
SortednessChecker::checkSort(vector<shared_ptr<Symbol>> &params,
                             shared_ptr<Sort> sort,
                             shared_ptr<AstNode> source,
                             shared_ptr<SortednessChecker::NodeError> err) {
    string name = sort->getIdentifier()->toString();
    bool isParam = false;
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        if (name == (*paramIt)->toString())
            isParam = true;
    }

    if (!isParam) {
        shared_ptr<SortInfo> info = ctx->getStack()->getSortInfo(name);
        if (!info) {
            err = addError(ErrorMessages::buildSortUnknown(name, sort->getRowLeft(), sort->getColLeft(),
                                                           sort->getRowRight(), sort->getColRight()), source, err);

            vector<shared_ptr<Sort>> argSorts = sort->getArgs();
            for (auto sortIt = argSorts.begin(); sortIt != argSorts.end(); sortIt++) {
                checkSort(params, *sortIt, source, err);
            }
        } else {
            if (sort->getArgs().empty())
                return err;

            if (sort->getArgs().size() != info->arity) {
                err = addError(ErrorMessages::buildSortArity(name, info->arity, sort->getArgs().size(),
                                                             sort->getRowLeft(), sort->getColLeft(),
                                                             sort->getRowRight(), sort->getColRight()),
                               source, info, err);
            } else {
                vector<shared_ptr<Sort>> argSorts = sort->getArgs();
                for (auto sortIt = argSorts.begin(); sortIt != argSorts.end(); sortIt++) {
                    checkSort(params, *sortIt, source, err);
                }
            }
        }
    }

    return err;
}

void SortednessChecker::visit(shared_ptr<AssertCommand> node) {
    TermSorter sorter(shared_from_this());
    shared_ptr<Sort> result = sorter.run(node->getTerm());
    if (result) {
        string resstr = result->toString();
        if (resstr != SORT_BOOL) {
            shared_ptr<Term> term = node->getTerm();
            addError(ErrorMessages::buildAssertTermNotBool(term->toString(), resstr,
                                                           term->getRowLeft(), term->getColLeft(),
                                                           term->getRowRight(), term->getColRight()), node);
        }
    } else {
        shared_ptr<Term> term = node->getTerm();
        addError(ErrorMessages::buildAssertTermNotWellSorted(term->toString(),
                                                             term->getRowLeft(), term->getColLeft(),
                                                             term->getRowRight(), term->getColRight()), node);
    }
}

void SortednessChecker::visit(shared_ptr<DeclareConstCommand> node) {
    shared_ptr<NodeError> err;
    err = checkSort(node->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = ctx->getStack()->tryAdd(nodeInfo);

    if (dupInfo) {
        addError(ErrorMessages::buildConstAlreadyExists(nodeInfo->name), node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<DeclareFunCommand> node) {
    shared_ptr<NodeError> err;

    vector<shared_ptr<Sort>> params = node->getParams();
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        err = checkSort(*paramIt, node, err);
    }

    err = checkSort(node->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = ctx->getStack()->tryAdd(nodeInfo);

    if (dupInfo) {
        addError(ErrorMessages::buildFunAlreadyExists(nodeInfo->name), node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<DeclareDatatypeCommand> node) {
    shared_ptr<NodeError> err;

    shared_ptr<ParametricDatatypeDeclaration> pdecl =
            dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->getDeclaration());

    vector<shared_ptr<SymbolInfo>> infos = getInfo(node);
    for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
        shared_ptr<SortInfo> sortInfo = dynamic_pointer_cast<SortInfo>(*infoIt);
        if (sortInfo) {
            shared_ptr<SortInfo> dupInfo = ctx->getStack()->tryAdd(sortInfo);

            if (dupInfo) {
                err = addError(ErrorMessages::buildSortAlreadyExists(sortInfo->name), node, dupInfo, err);
            }
        }
    }

    if (pdecl) {
        vector<shared_ptr<ConstructorDeclaration>> constructors = pdecl->getConstructors();

        for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
            vector<shared_ptr<SelectorDeclaration>> selectors = (*consIt)->getSelectors();

            for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                err = checkSort(pdecl->getParams(), (*selIt)->getSort(), node, err);
            }
        }
    } else {
        shared_ptr<SimpleDatatypeDeclaration> sdecl =
                dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->getDeclaration());
        vector<shared_ptr<ConstructorDeclaration>> constructors = sdecl->getConstructors();

        for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
            vector<shared_ptr<SelectorDeclaration>> selectors = (*consIt)->getSelectors();

            for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                err = checkSort((*selIt)->getSort(), node, err);
            }
        }
    }

    infos = getInfo(node);
    for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
        shared_ptr<FunInfo> funInfo = dynamic_pointer_cast<FunInfo>(*infoIt);
        if (funInfo) {
            shared_ptr<FunInfo> dupInfo = ctx->getStack()->tryAdd(funInfo);

            if (dupInfo) {
                err = addError(ErrorMessages::buildFunAlreadyExists(funInfo->name), node, dupInfo, err);
            }

        }
    }
}

void SortednessChecker::visit(shared_ptr<DeclareDatatypesCommand> node) {
    shared_ptr<NodeError> err;

    vector<shared_ptr<SymbolInfo>> infos = getInfo(node);
    for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
        shared_ptr<SortInfo> sortInfo = dynamic_pointer_cast<SortInfo>((*infoIt));
        if (sortInfo) {
            shared_ptr<SortInfo> dupInfo = ctx->getStack()->tryAdd(sortInfo);
            if (dupInfo) {
                err = addError(ErrorMessages::buildSortAlreadyExists(sortInfo->name), node, dupInfo, err);
            }
        }
    }

    for (unsigned long i = 0; i < node->getSorts().size(); i++) {
        shared_ptr<NodeError> declerr;

        shared_ptr<ParametricDatatypeDeclaration> pdecl =
                dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->getDeclarations()[i]);

        if (pdecl) {
            vector<shared_ptr<ConstructorDeclaration>> constructors = pdecl->getConstructors();

            for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
                vector<shared_ptr<SelectorDeclaration>> selectors = (*consIt)->getSelectors();

                for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                    declerr = checkSort(pdecl->getParams(), (*selIt)->getSort(), pdecl, declerr);
                }
            }
        } else {
            shared_ptr<SimpleDatatypeDeclaration> sdecl =
                    dynamic_pointer_cast<SimpleDatatypeDeclaration>(node->getDeclarations()[i]);
            vector<shared_ptr<ConstructorDeclaration>> constructors = sdecl->getConstructors();

            for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
                vector<shared_ptr<SelectorDeclaration>> selectors = (*consIt)->getSelectors();

                for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
                    declerr = checkSort((*selIt)->getSort(), sdecl, declerr);
                }
            }
        }
    }

    infos = getInfo(node);
    for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
        shared_ptr<FunInfo> funInfo = dynamic_pointer_cast<FunInfo>(*infoIt);

        if (funInfo) {
            shared_ptr<FunInfo> dupInfo = ctx->getStack()->tryAdd(funInfo);
            if (dupInfo) {
                err = addError(ErrorMessages::buildFunAlreadyExists(funInfo->name), node, dupInfo, err);
            }
        }
    }
}

void SortednessChecker::visit(shared_ptr<DeclareSortCommand> node) {
    shared_ptr<SortInfo> nodeInfo = getInfo(node);
    shared_ptr<SortInfo> dupInfo = ctx->getStack()->tryAdd(nodeInfo);

    if (dupInfo) {
        addError(ErrorMessages::buildSortAlreadyExists(nodeInfo->name), node, dupInfo);
    }
}

void SortednessChecker::visit(shared_ptr<DefineFunCommand> node) {
    shared_ptr<NodeError> err;

    vector<shared_ptr<SortedVariable>> sig = node->getDefinition()->getSignature()->getParams();
    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        err = checkSort((*sortIt)->getSort(), node, err);
    }
    err = checkSort(node->getDefinition()->getSignature()->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = ctx->getStack()->findDuplicate(nodeInfo);

    if (dupInfo) {
        addError(ErrorMessages::buildFunAlreadyExists(nodeInfo->name), node, dupInfo, err);
    } else {
        ctx->getStack()->push();

        vector<shared_ptr<SortedVariable>> &bindings = node->getDefinition()->getSignature()->getParams();
        for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
            ctx->getStack()->tryAdd(make_shared<VarInfo>((*bindingIt)->getSymbol()->toString(),
                                               ctx->getStack()->expand((*bindingIt)->getSort()), node));
        }

        TermSorter sorter(shared_from_this());
        shared_ptr<Sort> result = sorter.run(node->getDefinition()->getBody());

        if (result) {
            string retstr = nodeInfo->signature[nodeInfo->signature.size() - 1]->toString();
            string resstr = result->toString();
            if (resstr != retstr) {
                shared_ptr<Term> body = node->getDefinition()->getBody();
                addError(ErrorMessages::buildFunBodyWrongSort(body->toString(), resstr, retstr,
                                                              body->getRowLeft(), body->getColLeft(),
                                                              body->getRowRight(), body->getColRight()), node);
            }
        } else {
            shared_ptr<Term> body = node->getDefinition()->getBody();
            addError(ErrorMessages::buildFunBodyNotWellSorted(body->toString(),
                                                              body->getRowLeft(), body->getColLeft(),
                                                              body->getRowRight(), body->getColRight()), node);
        }

        ctx->getStack()->pop();        ctx->getStack()->tryAdd(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<DefineFunRecCommand> node) {
    shared_ptr<NodeError> err;

    vector<shared_ptr<SortedVariable>> sig = node->getDefinition()->getSignature()->getParams();
    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        err = checkSort((*sortIt)->getSort(), node, err);
    }
    err = checkSort(node->getDefinition()->getSignature()->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = ctx->getStack()->findDuplicate(nodeInfo);

    if (dupInfo) {
        addError(ErrorMessages::buildFunAlreadyExists(nodeInfo->name), node, dupInfo, err);
    } else {
        ctx->getStack()->push();
        ctx->getStack()->tryAdd(nodeInfo);

        vector<shared_ptr<SortedVariable>> &bindings = node->getDefinition()->getSignature()->getParams();
        for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
            ctx->getStack()->tryAdd(make_shared<VarInfo>((*bindingIt)->getSymbol()->toString(),
                                               ctx->getStack()->expand((*bindingIt)->getSort()), node));
        }

        TermSorter sorter(shared_from_this());
        shared_ptr<Sort> result = sorter.run(node->getDefinition()->getBody());

        if (result) {
            string retstr = nodeInfo->signature[nodeInfo->signature.size() - 1]->toString();
            string resstr = result->toString();
            if (resstr != retstr) {
                shared_ptr<Term> body = node->getDefinition()->getBody();
                addError(ErrorMessages::buildFunBodyWrongSort(body->toString(), resstr, retstr,
                                                              body->getRowLeft(), body->getColLeft(),
                                                              body->getRowRight(), body->getColRight()), node);
            }
        } else {
            shared_ptr<Term> body = node->getDefinition()->getBody();
            addError(ErrorMessages::buildFunBodyNotWellSorted(body->toString(),
                                                              body->getRowLeft(), body->getColLeft(),
                                                              body->getRowRight(), body->getColRight()), node);
        }

        ctx->getStack()->pop();
        ctx->getStack()->tryAdd(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<DefineFunsRecCommand> node) {
    shared_ptr<NodeError> err;
    vector<shared_ptr<FunctionDeclaration>> &decls = node->getDeclarations();
    vector<shared_ptr<Term>> &bodies = node->getBodies();

    for (auto declIt = decls.begin(); declIt != decls.end(); declIt++) {
        vector<shared_ptr<SortedVariable>> sig = (*declIt)->getParams();
        for (auto itt = sig.begin(); itt != sig.end(); itt++) {
            err = checkSort((*itt)->getSort(), node, err);
        }
        err = checkSort((*declIt)->getSort(), node, err);
    }

    vector<shared_ptr<FunInfo>> infos = getInfo(node);

    bool dup = false;
    for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
        shared_ptr<FunInfo> dupInfo = ctx->getStack()->findDuplicate(*infoIt);
        if (dupInfo) {
            dup = true;
            err = addError(ErrorMessages::buildFunAlreadyExists((*infoIt)->name), node, *infoIt, err);
        }
    }

    if (!dup) {
        ctx->getStack()->push();

        for (unsigned long i = 0; i < decls.size(); i++) {
            ctx->getStack()->tryAdd(infos[i]);
        }

        for (unsigned long i = 0; i < decls.size(); i++) {
            ctx->getStack()->push();
            vector<shared_ptr<SortedVariable>> &bindings = decls[i]->getParams();
            for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
                ctx->getStack()->tryAdd(make_shared<VarInfo>((*bindingIt)->getSymbol()->toString(),
                                                   ctx->getStack()->expand((*bindingIt)->getSort()), node));
            }

            TermSorter sorter(shared_from_this());
            shared_ptr<Sort> result = sorter.run(bodies[i]);

            if (result) {
                string retstr = infos[i]->signature[infos[i]->signature.size() - 1]->toString();
                string resstr = result->toString();
                if (resstr != retstr) {
                    err = addError(ErrorMessages::buildFunBodyWrongSort(infos[i]->name, infos[i]->body->toString(),
                                                                        resstr, retstr, infos[i]->body->getRowLeft(),
                                                                        infos[i]->body->getColLeft(),
                                                                        infos[i]->body->getRowRight(),
                                                                        infos[i]->body->getColRight()), node, err);
                }
            } else {
                err = addError(ErrorMessages::buildFunBodyNotWellSorted(infos[i]->name, infos[i]->body->toString(),
                                                                        infos[i]->body->getRowLeft(),
                                                                        infos[i]->body->getColLeft(),
                                                                        infos[i]->body->getRowRight(),
                                                                        infos[i]->body->getColRight()), node, err);
            }
            ctx->getStack()->pop();
        }

        ctx->getStack()->pop();
        for (unsigned long i = 0; i < infos.size(); i++) {
            ctx->getStack()->tryAdd(infos[i]);
        }
    }
}

void SortednessChecker::visit(shared_ptr<DefineSortCommand> node) {
    shared_ptr<NodeError> err;
    err = checkSort(node->getParams(), node->getSort(), node, err);

    shared_ptr<SortInfo> nodeInfo = getInfo(node);
    shared_ptr<SortInfo> dupInfo = ctx->getStack()->tryAdd(nodeInfo);

    if (dupInfo) {
        addError(ErrorMessages::buildSortAlreadyExists(nodeInfo->name), node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<GetValueCommand> node) {
    shared_ptr<NodeError> err;

    vector<shared_ptr<Term>> terms = node->getTerms();
    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        TermSorter sorter(shared_from_this());
        shared_ptr<Sort> result = sorter.run(*termIt);
        if (!result) {
            err = addError(ErrorMessages::buildTermNotWellSorted(
                    (*termIt)->toString(), (*termIt)->getRowLeft(),
                    (*termIt)->getColLeft(), (*termIt)->getRowRight(),
                    (*termIt)->getColRight()), node, err);
        }
    }
}

void SortednessChecker::visit(shared_ptr<PopCommand> node) {
    unsigned long levels = (unsigned long) node->getNumeral()->getValue();
    if (!ctx->getStack()->pop(levels)) {
        addError(ErrorMessages::buildStackUnpoppable(levels), node);
    }
}

void SortednessChecker::visit(shared_ptr<PushCommand> node) {
    ctx->getStack()->push((unsigned long) node->getNumeral()->getValue());
}

void SortednessChecker::visit(shared_ptr<ResetCommand> node) {
    ctx->getStack()->reset();
    ctx->setCurrentLogic("");
    ctx->getCurrentTheories().clear();
}

void SortednessChecker::visit(shared_ptr<SetLogicCommand> node) {
    shared_ptr<NodeError> err;
    if (ctx->getCurrentLogic() != "") {
        addError(ErrorMessages::buildLogicAlreadySet(ctx->getCurrentLogic()), node);
    } else {
        string logic = node->getLogic()->toString();
        ctx->setCurrentLogic(logic);
        loadLogic(logic, node, err);
    }
}

void SortednessChecker::visit(shared_ptr<Logic> node) {
    vector<shared_ptr<Attribute>> attrs = node->getAttributes();
    for (auto attrIt = attrs.begin(); attrIt != attrs.end(); attrIt++) {
        shared_ptr<Attribute> attr = *attrIt;
        if (attr->getKeyword()->getValue() == KW_THEORIES) {
            shared_ptr<NodeError> err;

            shared_ptr<CompAttributeValue> attrValue =
                    dynamic_pointer_cast<CompAttributeValue>(attr->getValue());
            vector<shared_ptr<AttributeValue>> compValues = attrValue->getValues();

            for (auto valIt = compValues.begin(); valIt != compValues.end(); valIt++) {
                string theory = dynamic_cast<Symbol *>((*valIt).get())->toString();
                auto found = find(ctx->getCurrentTheories().begin(), ctx->getCurrentTheories().end(), theory);

                if (found != ctx->getCurrentTheories().end()) {
                    err = addError(ErrorMessages::buildTheoryAlreadyLoaded(theory), attr, err);
                } else {
                    ctx->getCurrentTheories().push_back(theory);
                    loadTheory(theory, attr, err);
                }
            }
        }
    }
}

void SortednessChecker::visit(shared_ptr<Theory> node) {
    vector<shared_ptr<Attribute>> attrs = node->getAttributes();
    for (auto attrIt = attrs.begin(); attrIt != attrs.end(); attrIt++) {
        shared_ptr<Attribute> attr = *attrIt;

        if (attr->getKeyword()->getValue() == KW_SORTS || attr->getKeyword()->getValue() == KW_FUNS) {
            CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
            visit0(val->getValues());
        }
    }
}

void SortednessChecker::visit(shared_ptr<Script> node) {
    visit0(node->getCommands());
}

void SortednessChecker::visit(shared_ptr<SortSymbolDeclaration> node) {
    shared_ptr<SortInfo> nodeInfo = getInfo(node);
    shared_ptr<SortInfo> dupInfo = ctx->getStack()->tryAdd(nodeInfo);

    if (dupInfo) {
        addError(ErrorMessages::buildSortAlreadyExists(nodeInfo->name), node, dupInfo);
    }
}

void SortednessChecker::visit(shared_ptr<SpecConstFunDeclaration> node) {
    shared_ptr<NodeError> err;
    err = checkSort(node->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    shared_ptr<FunInfo> dupInfo = ctx->getStack()->tryAdd(nodeInfo);

    if (dupInfo) {
        addError(ErrorMessages::buildSpecConstAlreadyExists(nodeInfo->name), node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<MetaSpecConstFunDeclaration> node) {
    shared_ptr<NodeError> err;
    err = checkSort(node->getSort(), node, err);

    shared_ptr<FunInfo> nodeInfo = getInfo(node);
    vector<shared_ptr<FunInfo>> dupInfo = ctx->getStack()->getFunInfo(nodeInfo->name);

    if (!dupInfo.empty()) {
        err = addError(ErrorMessages::buildMetaSpecConstAlreadyExists(nodeInfo->name), node, dupInfo[0], err);
    } else {
        ctx->getStack()->tryAdd(nodeInfo);
    }
}

void SortednessChecker::visit(shared_ptr<SimpleFunDeclaration> node) {
    shared_ptr<NodeError> err;

    vector<shared_ptr<Sort>> sig = node->getSignature();
    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        err = checkSort(*sortIt, node, err);
    }

    shared_ptr<FunInfo> nodeInfo = getInfo(node);

    if (nodeInfo->assocL) {
        if (sig.size() != 3) {
            err = addError(ErrorMessages::buildLeftAssocParamCount(nodeInfo->name), node, err);
            nodeInfo->assocL = false;
        } else {
            shared_ptr<Sort> firstSort = sig[0];
            shared_ptr<Sort> returnSort = sig[2];

            if (firstSort->toString() != returnSort->toString()) {
                err = addError(ErrorMessages::buildLeftAssocRetSort(nodeInfo->name), node, err);
                nodeInfo->assocL = false;
            }
        }
    }

    if (nodeInfo->assocR) {
        if (sig.size() != 3) {
            err = addError(ErrorMessages::buildRightAssocParamCount(nodeInfo->name), node, err);
            nodeInfo->assocR = false;
        } else {
            shared_ptr<Sort> secondSort = sig[1];
            shared_ptr<Sort> returnSort = sig[2];

            if (secondSort->toString() != returnSort->toString()) {
                err = addError(ErrorMessages::buildRightAssocRetSort(nodeInfo->name), node, err);
                nodeInfo->assocR = false;
            }
        }
    }

    if (nodeInfo->chainable && nodeInfo->pairwise) {
        err = addError(ErrorMessages::buildChainableAndPairwise(nodeInfo->name), node, err);
        nodeInfo->chainable = false;
        nodeInfo->pairwise = false;
    } else if (nodeInfo->chainable) {
        if (sig.size() != 3) {
            err = addError(ErrorMessages::buildChainableParamCount(nodeInfo->name), node, err);
            nodeInfo->chainable = false;
        } else {
            shared_ptr<Sort> firstSort = sig[0];
            shared_ptr<Sort> secondSort = sig[1];
            shared_ptr<Sort> returnSort = sig[2];

            if (firstSort->toString() != secondSort->toString()) {
                err = addError(ErrorMessages::buildChainableParamSort(nodeInfo->name), node, err);
                nodeInfo->chainable = false;
            }

            if (returnSort->toString() != SORT_BOOL) {
                err = addError(ErrorMessages::buildChainableRetSort(nodeInfo->name), node, err);
                nodeInfo->chainable = false;
            }
        }
    } else if (nodeInfo->pairwise) {
        if (sig.size() != 3) {
            err = addError(ErrorMessages::buildPairwiseParamCount(nodeInfo->name), node, err);
            nodeInfo->pairwise = false;
        } else {
            shared_ptr<Sort> firstSort = sig[0];
            shared_ptr<Sort> secondSort = sig[1];
            shared_ptr<Sort> returnSort = sig[2];

            if (firstSort->toString() != secondSort->toString()) {
                err = addError(ErrorMessages::buildPairwiseParamSort(nodeInfo->name), node, err);
                nodeInfo->pairwise = false;
            }

            if (returnSort->toString() != SORT_BOOL) {
                err = addError(ErrorMessages::buildPairwiseRetSort(nodeInfo->name), node, err);
                nodeInfo->pairwise = false;
            }
        }
    }

    shared_ptr<FunInfo> dupInfo = ctx->getStack()->tryAdd(nodeInfo);

    if (dupInfo) {
        addError(ErrorMessages::buildFunAlreadyExists(nodeInfo->name), node, dupInfo, err);
    }
}

void SortednessChecker::visit(shared_ptr<ParametricFunDeclaration> node) {
    shared_ptr<NodeError> err;

    vector<shared_ptr<Sort>> sig = node->getSignature();
    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        err = checkSort(node->getParams(), *sortIt, node, err);
    }

    shared_ptr<FunInfo> nodeInfo = getInfo(node);

    if (nodeInfo->assocL) {
        if (sig.size() != 3) {
            err = addError(ErrorMessages::buildLeftAssocParamCount(nodeInfo->name), node, err);
            nodeInfo->assocL = false;
        } else {
            shared_ptr<Sort> firstSort = sig[0];
            shared_ptr<Sort> returnSort = sig[2];

            if (firstSort->toString() != returnSort->toString()) {
                err = addError(ErrorMessages::buildLeftAssocRetSort(nodeInfo->name), node, err);
                nodeInfo->assocL = false;
            }
        }
    }

    if (nodeInfo->assocR) {
        if (sig.size() != 3) {
            err = addError(ErrorMessages::buildRightAssocParamCount(nodeInfo->name), node, err);
            nodeInfo->assocR = false;
        } else {
            shared_ptr<Sort> secondSort = sig[1];
            shared_ptr<Sort> returnSort = sig[2];

            if (secondSort->toString() != returnSort->toString()) {
                err = addError(ErrorMessages::buildRightAssocRetSort(nodeInfo->name), node, err);
                nodeInfo->assocR = false;
            }
        }
    }

    if (nodeInfo->chainable && nodeInfo->pairwise) {
        err = addError(ErrorMessages::buildChainableAndPairwise(nodeInfo->name), node, err);
        nodeInfo->chainable = false;
        nodeInfo->pairwise = false;
    } else if (nodeInfo->chainable) {
        if (sig.size() != 3) {
            err = addError(ErrorMessages::buildChainableParamCount(nodeInfo->name), node, err);
            nodeInfo->chainable = false;
        } else {
            shared_ptr<Sort> firstSort = sig[0];
            shared_ptr<Sort> secondSort = sig[1];
            shared_ptr<Sort> returnSort = sig[2];

            if (firstSort->toString() != secondSort->toString()) {
                err = addError(ErrorMessages::buildChainableParamSort(nodeInfo->name), node, err);
                nodeInfo->chainable = false;
            }

            if (returnSort->toString() != SORT_BOOL) {
                err = addError(ErrorMessages::buildChainableRetSort(nodeInfo->name), node, err);
                nodeInfo->chainable = false;
            }
        }
    } else if (nodeInfo->pairwise) {
        if (sig.size() != 3) {
            err = addError(ErrorMessages::buildPairwiseParamCount(nodeInfo->name), node, err);
            nodeInfo->pairwise = false;
        } else {
            shared_ptr<Sort> firstSort = sig[0];
            shared_ptr<Sort> secondSort = sig[1];
            shared_ptr<Sort> returnSort = sig[2];

            if (firstSort->toString() != secondSort->toString()) {
                err = addError(ErrorMessages::buildPairwiseParamSort(nodeInfo->name), node, err);
                nodeInfo->pairwise = false;
            }

            if (returnSort->toString() != SORT_BOOL) {
                err = addError(ErrorMessages::buildPairwiseRetSort(nodeInfo->name), node, err);
                nodeInfo->pairwise = false;
            }
        }
    }

    shared_ptr<FunInfo> dupInfo = ctx->getStack()->tryAdd(nodeInfo);

    if (dupInfo) {
        addError(ErrorMessages::buildFunAlreadyExists(nodeInfo->name), node, dupInfo, err);
    }
}

bool SortednessChecker::check(shared_ptr<AstNode> node) {
    if (node) {
        visit0(node);
    } else {
        Logger::warning("SortednessChecker::run()", "Attempting to check an empty abstract syntax tree");
        return false;
    }
    return errors.empty();
}

string SortednessChecker::getErrors() {
    stringstream ss;

    for (auto errIt = errors.begin(); errIt != errors.end(); errIt++) {
        string file = errIt->first;
        vector<shared_ptr<NodeError>> errs = errIt->second;

        if (file != "") {
            long length = 11 + file.length();
            for (long i = 0; i < length; i++)
                ss << "-";
            ss << endl << "In file '" << file << "':" << endl;
            for (long i = 0; i < length; i++)
                ss << "-";
            ss << endl;
        }

        for (auto itt = errs.begin(); itt != errs.end(); itt++) {
            shared_ptr<NodeError> err = *itt;
            if (err->node) {
                ss << err->node->getRowLeft() << ":" << err->node->getColLeft()
                << " - " << err->node->getRowRight() << ":" << err->node->getColRight() << "   ";

                string nodestr = err->node->toString();
                if (nodestr.length() > 100)
                    ss << string(nodestr, 0, 100) << "[...]";
                else
                    ss << nodestr;

                ss << endl;
            }

            for (auto infoIt = err->errs.begin(); infoIt != err->errs.end(); infoIt++) {
                shared_ptr<AstNode> source;

                if ((*infoIt)->info) {
                    source = (*infoIt)->info->source;
                }

                if (infoIt != err->errs.begin() && source)
                    ss << endl;

                ss << "\t" << (*infoIt)->message << "." << endl;

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

                    if (infoIt + 1 != err->errs.end())
                        ss << endl;
                }
            }

            ss << endl;
        }
    }

    ss << endl;

    return ss.str();
}

shared_ptr<SymbolStack> SortednessChecker::getStack() {
    return ctx->getStack();
}

shared_ptr<SortednessChecker> SortednessChecker::getChecker() {
    return shared_from_this();
}

