#include "ast_term_sorter.h"
#include "ast_sortedness_checker.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_theory.h"
#include "../parser/smt_parser.h"
#include "../util/global_settings.h"
#include "../util/error_messages.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

void TermSorter::visit(shared_ptr<SimpleIdentifier> node) {
    shared_ptr<VarInfo> varInfo = ctx->getStack()->getVarInfo(node->toString());
    if (varInfo) {
        ret = varInfo->sort;
    } else {
        vector<shared_ptr<FunInfo>> infos = ctx->getStack()->getFunInfo(node->toString());
        vector<shared_ptr<Sort>> possibleSorts;
        for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
            if ((*infoIt)->signature.size() == 1 && (*infoIt)->params.empty())
                possibleSorts.push_back((*infoIt)->signature[0]);
        }

        if (possibleSorts.size() == 1) {
            ret = possibleSorts[0];
        } else if (possibleSorts.empty()) {
            ctx->getChecker()->addError((node->toString()), node);
        } else {
            vector<string> possibleSortsStr;
            for (auto sort : possibleSorts) {
                possibleSortsStr.push_back(sort->toString());
            }
            ctx->getChecker()->addError(
                    ErrorMessages::buildConstMultipleSorts(node->toString(),
                                                           possibleSortsStr), node);
        }
    }
}

void TermSorter::visit(shared_ptr<QualifiedIdentifier> node) {
    shared_ptr<SortednessChecker::NodeError> err;
    err = ctx->getChecker()->checkSort(node->getSort(), node, err);

    vector<shared_ptr<FunInfo>> infos = ctx->getStack()->getFunInfo(node->getIdentifier()->toString());
    shared_ptr<Sort> retExpanded = ctx->getStack()->expand(node->getSort());

    vector<shared_ptr<Sort>> retSorts;
    for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
        if ((*infoIt)->signature.size() == 1) {
            if ((*infoIt)->params.empty()) {
                retSorts.push_back((*infoIt)->signature[0]);
            } else {
                vector<string> pnames;
                for (auto p = (*infoIt)->params.begin(); p != (*infoIt)->params.end(); p++) {
                    pnames.push_back((*p)->toString());
                }

                unordered_map<string, shared_ptr<Sort>> mapping;
                getParamMapping(pnames, mapping, (*infoIt)->signature[0], retExpanded);

                if (mapping.size() == pnames.size()) {
                    shared_ptr<Sort> retSort = ctx->getStack()->replace((*infoIt)->signature[0], mapping);
                    if (retSort->toString() == retExpanded->toString()) {
                        ret = retSort;
                        return;
                    }
                    retSorts.push_back(retSort);
                }
            }
        }
    }

    if (retSorts.size() == 1 && retSorts[0]->toString() == retExpanded->toString()) {
        ret = retSorts[0];
    } else {
        if (retSorts.empty()) {
            err = ctx->getChecker()->addError(
                    ErrorMessages::buildConstUnknown(node->getIdentifier()->toString()), node, err);
        } else {
            vector<string> retSortsStr;
            for (auto sort : retSorts) {
                retSortsStr.push_back(sort->toString());
            }
            ctx->getChecker()->addError(
                    ErrorMessages::buildConstWrongSort(node->getIdentifier()->toString(),
                                                       retExpanded->toString(), retSortsStr), node, err);
        }
    }
}

void TermSorter::visit(shared_ptr<DecimalLiteral> node) {
    vector<shared_ptr<FunInfo>> infos = ctx->getStack()->getFunInfo(MSCONST_DECIMAL);
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        if (infos.empty()) {
            ctx->getChecker()->addError(ErrorMessages::buildLiteralUnknownSort(MSCONST_DECIMAL_REF), node);
        } else {
            vector<string> possibleSorts;
            for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
                if ((*infoIt)->signature.size() == 1 && (*infoIt)->params.empty())
                    possibleSorts.push_back((*infoIt)->signature[0]->toString());
            }
            ctx->getChecker()->addError(
                    ErrorMessages::buildLiteralMultipleSorts(MSCONST_DECIMAL_REF, possibleSorts), node);
        }
    }
}

void TermSorter::visit(shared_ptr<NumeralLiteral> node) {
    vector<shared_ptr<FunInfo>> infos = ctx->getStack()->getFunInfo(MSCONST_NUMERAL);
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        if (infos.empty()) {
            ctx->getChecker()->addError(ErrorMessages::buildLiteralUnknownSort(MSCONST_NUMERAL_REF), node);
        } else {
            vector<string> possibleSorts;
            for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
                if ((*infoIt)->signature.size() == 1 && (*infoIt)->params.empty())
                    possibleSorts.push_back((*infoIt)->signature[0]->toString());
            }
            ctx->getChecker()->addError(
                    ErrorMessages::buildLiteralMultipleSorts(MSCONST_NUMERAL_REF, possibleSorts), node);
        }
    }
}

void TermSorter::visit(shared_ptr<StringLiteral> node) {
    vector<shared_ptr<FunInfo>> infos = ctx->getStack()->getFunInfo(MSCONST_STRING);
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        if (infos.empty()) {
            ctx->getChecker()->addError(ErrorMessages::buildLiteralUnknownSort(MSCONST_STRING_REF), node);
        } else {
            vector<string> possibleSorts;
            for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
                if ((*infoIt)->signature.size() == 1 && (*infoIt)->params.empty())
                    possibleSorts.push_back((*infoIt)->signature[0]->toString());
            }
            ctx->getChecker()->addError(
                    ErrorMessages::buildLiteralMultipleSorts(MSCONST_STRING_REF, possibleSorts), node);
        }
    }
}

void TermSorter::visit(shared_ptr<QualifiedTerm> node) {
    shared_ptr<SortednessChecker::NodeError> err;

    vector<shared_ptr<Sort>> argSorts;
    vector<shared_ptr<Term>> terms = node->getTerms();
    for (auto termIt = terms.begin(); termIt != terms.end(); termIt++) {
        shared_ptr<Sort> result = wrappedVisit(*termIt);
        if (result)
            argSorts.push_back(result);
        else {
            return;
        }
    }

    shared_ptr<SimpleIdentifier> id = dynamic_pointer_cast<SimpleIdentifier>(node->getIdentifier());
    shared_ptr<QualifiedIdentifier> qid = dynamic_pointer_cast<QualifiedIdentifier>(node->getIdentifier());

    shared_ptr<Sort> retExpanded;
    string name;

    if (id) {
        name = id->toString();
    } else {
        err = ctx->getChecker()->checkSort(qid->getSort(), node, err);
        name = qid->getIdentifier()->toString();
        retExpanded = ctx->getStack()->expand(qid->getSort());
    }

    vector<shared_ptr<FunInfo>> infos = ctx->getStack()->getFunInfo(name);
    vector<shared_ptr<Sort>> retSorts;


    for (auto infoIt = infos.begin(); infoIt != infos.end(); infoIt++) {
        vector<shared_ptr<Sort>> funSig;
        if (argSorts.size() >= 2) {
            if ((*infoIt)->assocL) {
                funSig.push_back((*infoIt)->signature[0]);
                for (int i = 0; i < argSorts.size() - 1; i++) {
                    funSig.push_back((*infoIt)->signature[1]);
                }
                funSig.push_back((*infoIt)->signature[2]);
            } else if ((*infoIt)->assocR) {
                for (int i = 0; i < argSorts.size() - 1; i++) {
                    funSig.push_back((*infoIt)->signature[0]);
                }
                funSig.push_back((*infoIt)->signature[1]);
                funSig.push_back((*infoIt)->signature[2]);
            } else if ((*infoIt)->chainable || (*infoIt)->pairwise) {
                for (int i = 0; i < argSorts.size(); i++) {
                    funSig.push_back((*infoIt)->signature[0]);
                }
                funSig.push_back((*infoIt)->signature[2]);
            } else {
                funSig.insert(funSig.begin(), (*infoIt)->signature.begin(), (*infoIt)->signature.end());
            }
        } else {
            funSig.insert(funSig.begin(), (*infoIt)->signature.begin(), (*infoIt)->signature.end());
        }

        if (argSorts.size() == funSig.size() - 1) {
            bool fits = true;
            if ((*infoIt)->params.empty()) {
                for (unsigned long i = 0; i < funSig.size() - 1; i++) {
                    if (funSig[i]->toString() != argSorts[i]->toString())
                        fits = false;
                }

                if (id) {
                    if (fits)
                        retSorts.push_back(funSig[funSig.size() - 1]);
                } else {
                    shared_ptr<Sort> retSort = funSig[funSig.size() - 1];
                    if (fits && retSort->toString() == retExpanded->toString()) {
                        ret = retSort;
                        return;
                    }
                }
            } else {
                vector<string> pnames;
                for (auto p = (*infoIt)->params.begin(); p != (*infoIt)->params.end(); p++) {
                    pnames.push_back((*p)->toString());
                }
                unordered_map<string, shared_ptr<Sort>> mapping;

                for (unsigned long i = 0; i < funSig.size() - 1; i++) {
                    fits = fits && getParamMapping(pnames, mapping, funSig[i], argSorts[i]);
                }

                if (fits && mapping.size() == (*infoIt)->params.size()) {
                    shared_ptr<Sort> retSort = funSig[funSig.size() - 1];
                    retSort = ctx->getStack()->replace(retSort, mapping);
                    string retSortString = retSort->toString();
                    if (id) {
                        retSorts.push_back(retSort);
                    } else {
                        if (retSortString == retExpanded->toString()) {
                            ret = retSort;
                            return;
                        }
                    }
                }
            }
        }
    }

    vector<string> argSortsStr;
    for (auto sort : argSorts) {
        argSortsStr.push_back(sort->toString());
    }

    vector<string> retSortsStr;
    for (auto sort : retSorts) {
        retSortsStr.push_back(sort->toString());
    }

    if (id) {
        if (retSorts.size() == 1) {
            ret = retSorts[0];
        } else if (retSorts.empty()) {
            err = ctx->getChecker()->addError(
                    ErrorMessages::buildFunUnknownDecl(name, argSortsStr), node, err);
        } else {
            err = ctx->getChecker()->addError
                    (ErrorMessages::buildFunMultipleDecls(name, argSortsStr, retSortsStr), node, err);
        }
    } else {
        err = ctx->getChecker()->addError(
                ErrorMessages::buildFunUnknownDecl(name, argSortsStr, retExpanded->toString()), node, err);
    }
}

void TermSorter::visit(shared_ptr<LetTerm> node) {
    ctx->getStack()->push();

    vector<shared_ptr<VarBinding>> &bindings = node->getBindings();
    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        shared_ptr<Sort> result = wrappedVisit((*bindingIt)->getTerm());
        if (result) {
            ctx->getStack()->tryAdd(
                    make_shared<VarInfo>((*bindingIt)->getSymbol()->toString(), result, node));
        } else {
            return;
        }
    }

    shared_ptr<Sort> result = wrappedVisit(node->getTerm());
    if (result) {
        ret = result;
    }

    ctx->getStack()->pop();
}

void TermSorter::visit(shared_ptr<ForallTerm> node) {
    ctx->getStack()->push();

    vector<shared_ptr<SortedVariable>> &bindings = node->getBindings();
    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        ctx->getStack()->tryAdd(
                make_shared<VarInfo>((*bindingIt)->getSymbol()->toString(),
                                     ctx->getStack()->expand((*bindingIt)->getSort()), node));
    }

    shared_ptr<Sort> result = wrappedVisit(node->getTerm());
    if (result) {
        string resstr = result->toString();
        if (resstr == SORT_BOOL) {
            ret = result;
        } else {
            ctx->getChecker()->addError(
                    ErrorMessages::buildQuantTermWrongSort(node->getTerm()->toString(), resstr, SORT_BOOL,
                                                           node->getTerm()->getRowLeft(),
                                                           node->getTerm()->getColLeft(),
                                                           node->getTerm()->getRowRight(),
                                                           node->getTerm()->getColRight()), node);
        }
    }

    ctx->getStack()->pop();
}

void TermSorter::visit(shared_ptr<ExistsTerm> node) {
    ctx->getStack()->push();

    vector<shared_ptr<SortedVariable>> &bindings = node->getBindings();
    for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
        ctx->getStack()->tryAdd(
                make_shared<VarInfo>((*bindingIt)->getSymbol()->toString(),
                                     ctx->getStack()->expand((*bindingIt)->getSort()), node));
    }

    shared_ptr<Sort> result = wrappedVisit(node->getTerm());
    if (result) {
        string resstr = result->toString();
        if (resstr == SORT_BOOL) {
            ret = result;
        } else {
            ctx->getChecker()->addError(
                    ErrorMessages::buildQuantTermWrongSort(node->getTerm()->toString(), resstr, SORT_BOOL,
                                                           node->getTerm()->getRowLeft(),
                                                           node->getTerm()->getColLeft(),
                                                           node->getTerm()->getRowRight(),
                                                           node->getTerm()->getColRight()), node);
        }
    }

    ctx->getStack()->pop();
}

void TermSorter::visit(shared_ptr<MatchTerm> node) {
    shared_ptr<Sort> termSort = wrappedVisit(node->getTerm());
    vector<shared_ptr<Sort>> caseSorts;

    if (termSort) {
        shared_ptr<SortednessChecker::NodeError> err;
        string termSortStr = termSort->toString();

        vector<shared_ptr<MatchCase>> cases = node->getCases();
        for (auto caseIt = cases.begin(); caseIt != cases.end(); caseIt++) {
            shared_ptr<Pattern> pattern = (*caseIt)->getPattern();

            // symbol (constructor or variable)
            shared_ptr<Symbol> spattern = dynamic_pointer_cast<Symbol>(pattern);
            // qualified constructor
            shared_ptr<QualifiedConstructor> cpattern = dynamic_pointer_cast<QualifiedConstructor>(pattern);
            // qualified pattern
            shared_ptr<QualifiedPattern> qpattern = dynamic_pointer_cast<QualifiedPattern>(pattern);

            shared_ptr<Symbol> scons; // simple constructor for qualified pattern
            shared_ptr<QualifiedConstructor> qcons; // qualified constructor for qualified pattern
            string caseId;

            // Init caseId, scons, qcons
            if (spattern) {
                caseId = spattern->toString();
            } else if (cpattern) {
                caseId = cpattern->getSymbol()->toString();
            } else if (qpattern) {
                shared_ptr<Constructor> cons = qpattern->getConstructor();
                scons = dynamic_pointer_cast<Symbol>(cons);
                qcons = dynamic_pointer_cast<QualifiedConstructor>(cons);

                if (scons)
                    caseId = scons->toString();
                else
                    caseId = qcons->getSymbol()->toString();
            }

            // Get known information about functions with the name caseId
            vector<shared_ptr<FunInfo>> funInfos = ctx->getStack()->getFunInfo(caseId);
            vector<shared_ptr<FunInfo>> matchingInfos;
            vector<unordered_map<string, shared_ptr<Sort>>> matchingMappings;

            for (auto info = funInfos.begin(); info != funInfos.end(); info++) {
                shared_ptr<Sort> retSort = (*info)->signature[(*info)->signature.size() - 1];
                string retSortStr = retSort->toString();

                // If info is about a parametric function, map sort parameters to real sorts
                vector<string> pnames;
                unordered_map<string, shared_ptr<Sort>> mapping;
                bool mapped = true;

                if (!(*info)->params.empty()) {
                    for (auto p = (*info)->params.begin(); p != (*info)->params.end(); p++) {
                        pnames.push_back((*p)->toString());
                    }
                    mapped = getParamMapping(pnames, mapping, retSort, termSort);
                }

                // Check if current function info fits
                if (spattern || cpattern) {
                    // Return sort mismatch in case of qualified constructor
                    if (cpattern && cpattern->getSort()->toString() != termSortStr) {
                        err = ctx->getChecker()->addError(
                                ErrorMessages::buildPatternMismatch(termSortStr, pattern->toString()), node, err);
                        continue;
                    }

                    // If return sorts were mapped correctly
                    if (mapped && (*info)->params.size() == mapping.size()) {
                        matchingInfos.push_back(*info);
                        matchingMappings.push_back(mapping);
                    }
                } else if (qpattern) {
                    // Return sort mismatch in case of qualified constructor
                    if (qcons && qcons->getSort()->toString() != termSortStr) {
                        err = ctx->getChecker()->addError(
                                ErrorMessages::buildPatternMismatch(termSortStr, pattern->toString()), node, err);
                        continue;
                    }

                    // If return sorts were mapped correctly
                    // and there are as many arguments to the fuction as there are symbols in the pattern
                    if (mapped && (*info)->params.size() == mapping.size()
                        && qpattern->getSymbols().size() == (*info)->signature.size() - 1) {
                        matchingInfos.push_back(*info);
                        matchingMappings.push_back(mapping);
                    }
                }
            }

            if (matchingInfos.empty()) {
                if (spattern && caseIt + 1 == node->getCases().end()) {
                    // If it's not a function, try to interpret it as a variable
                    ctx->getStack()->push();
                    ctx->getStack()->tryAdd(make_shared<VarInfo>(caseId, termSort, *caseIt));
                    shared_ptr<Sort> caseSort = wrappedVisit((*caseIt)->getTerm());
                    if (caseSort) {
                        caseSorts.push_back(caseSort);
                    }
                    ctx->getStack()->pop();
                } else if (spattern || cpattern) {
                    err = ctx->getChecker()->addError(
                            ErrorMessages::buildFunUnknownDecl(caseId, termSort->toString()), node, err);
                } else if (qpattern) {
                    err = ctx->getChecker()->addError(
                            ErrorMessages::buildFunUnknownDecl(caseId, qpattern->getSymbols().size(),
                                                               termSort->toString()), node, err);
                }
            } else if (matchingInfos.size() > 1) {
                if (qpattern) {
                    err = ctx->getChecker()->addError(
                            ErrorMessages::buildFunMultipleDecls(caseId, qpattern->getSymbols().size(),
                                                                 termSort->toString()), node, err);
                }
            } else {
                shared_ptr<FunInfo> match = matchingInfos[0];
                if (qpattern) {
                    ctx->getStack()->push();
                    for (unsigned long i = 0; i < match->signature.size() - 1; i++) {
                        shared_ptr<Sort> paramSort = ctx->getStack()->replace(match->signature[i],
                                                                                    matchingMappings[0]);
                        ctx->getStack()->tryAdd(
                                make_shared<VarInfo>(qpattern->getSymbols()[i]->toString(), paramSort, *caseIt));
                    }
                }

                shared_ptr<Sort> caseSort = wrappedVisit((*caseIt)->getTerm());
                if (caseSort) {
                    caseSorts.push_back(caseSort);
                }

                if (qpattern) {
                    ctx->getStack()->pop();
                }
            }
        }

        vector<string> caseSortsStr;
        for (auto caseSort : caseSorts) {
            caseSortsStr.push_back(caseSort->toString());
        }

        if (caseSorts.size() == node->getCases().size()) {
            string case1 = caseSorts[0]->toString();
            bool equalCases = true;
            for (unsigned long i = 1; i < caseSorts.size(); i++) {
                if (caseSorts[1]->toString() != case1) {
                    err = ctx->getChecker()->addError(
                            ErrorMessages::buildCasesMismatch(caseSortsStr), node, err);
                    equalCases = false;
                    break;
                }
            }
            if (equalCases)
                ret = caseSorts[0];
        }
    }
}

void TermSorter::visit(shared_ptr<AnnotatedTerm> node) {
    visit0(node->getTerm());
}


bool TermSorter::getParamMapping(vector<string> &params,
                                 unordered_map<string, shared_ptr<Sort>> &mapping,
                                 shared_ptr<Sort> sort1,
                                 shared_ptr<Sort> sort2) {
    if (!sort1 || !sort2)
        return false;

    string sort1Name = sort1->getIdentifier()->toString();
    bool isParam = (find(params.begin(), params.end(), sort1Name) != params.end());

    if (isParam) {
        if (mapping[sort1Name]) {
            return mapping[sort1Name]->toString() == sort2->toString();
        } else {
            mapping[sort1Name] = sort2;
            return true;
        }
    } else {
        if (sort1->getArgs().size() != sort2->getArgs().size()) {
            return false;
        } else if (sort1->getArgs().empty()) {
            return sort1Name == sort2->getIdentifier()->toString();
        } else {
            string sort2Name = sort2->getIdentifier()->toString();

            if (sort1Name != sort2Name || sort1->getArgs().size() != sort2->getArgs().size()) {
                return false;
            }

            bool fits = true;
            for (unsigned long i = 0; i < sort1->getArgs().size(); i++) {
                fits = fits && getParamMapping(params, mapping, sort1->getArgs()[i], sort2->getArgs()[i]);
            }

            return fits;
        }
    }
}