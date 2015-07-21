#include "ast_sortedness_checker.h"
#include "ast_syntax_checker.h"
#include "../ast/ast_command.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_theory.h"
#include "../parser/smt_parser.h"
#include "../util/smt_logger.h"
#include "../util/global_settings.h"

#include <memory>
#include <sstream>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

string buildUnknownConstMsg(string name) {
    return "Unknown constant '" + name + "'";
}

string buildMultipleSortsConstMsg(string name,
                                  vector<shared_ptr<Sort>> &possibleSorts) {
    stringstream ss;
    ss << "Multiple possible sorts for constant '" << name << "': ";
    bool first = true;
    for (auto it : possibleSorts) {
        if (!first)
            ss << ", ";
        else
            first = false;
        ss << it->toString();
    }
    return ss.str();
}

string buildWrongSortConstMsg(string name,
                              shared_ptr<Sort> wrongSort,
                              vector<shared_ptr<Sort>> &possibleSorts) {
    stringstream ss;
    ss << "Constant '" << name << "' cannot be of sort " << wrongSort->toString()
    << ". Possible sorts: ";
    bool first = true;
    for (auto it : possibleSorts) {
        if (!first)
            ss << ", ";
        else
            first = false;
        ss << it->toString();
    }
    return ss.str();
}

string buildNoSortLiteralMsg(string literalType) {
    return "No declared sort for " + literalType + " literals";
}

string buildMultipleSortsLiteralMsg(string literalType,
                                    vector<shared_ptr<Sort>> &possibleSorts) {
    stringstream ss;
    ss << "Multiple declared sorts for " + literalType + " literals: ";
    bool first = true;
    for (auto it : possibleSorts) {
        if (!first)
            ss << ", ";
        else
            first = false;
        ss << it->toString();
    }
    return ss.str();
}

string buildNoDeclFunMsg(string name,
                         shared_ptr<Sort> retSort) {
    stringstream ss;
    ss << "No known declaration for function '" << name << "' with return sort " << retSort->toString();
    return ss.str();
}

string buildNoDeclFunMsg(string name,
                         unsigned long paramCount,
                         shared_ptr<Sort> retSort) {
    stringstream ss;
    ss << "No known declaration for function '" << name << "' with "
       << paramCount <<" parameters and return sort " << retSort->toString();
    return ss.str();
}

string buildNoDeclFunMsg(string name,
                         vector<shared_ptr<Sort>> argSorts) {
    stringstream ss;
    ss << "No known declaration for function '" << name << "' with parameter list (";
    bool first = true;
    for (auto it : argSorts) {
        if (first) {
            first = false;
        } else {
            ss << " ";
        }
        ss << it->toString();
    }
    ss << ")";
    return ss.str();
}

string buildNoDeclFunMsg(string name,
                         vector<shared_ptr<Sort>> argSorts,
                         shared_ptr<Sort> retSort) {
    stringstream ss;
    ss << buildNoDeclFunMsg(name, argSorts) << " and return sort " << retSort->toString();
    return ss.str();
}

string buildMultipleDeclFunMsg(string name,
                               unsigned long paramCount,
                               shared_ptr<Sort> retSort) {
    stringstream ss;
    ss << "Multiple declarations for function '" << name << "' with "
    << paramCount << " parameters and return sort " << retSort->toString();
    return ss.str();
}

string buildMultipleDeclFunMsg(string name,
                               vector<shared_ptr<Sort>> argSorts,
                               vector<shared_ptr<Sort>> retSorts) {
    stringstream ss;
    ss << "Multiple declarations for function '" << name << "' with parameter list ";
    bool first = true;
    for (auto it : argSorts) {
        if (first) {
            first = false;
        } else {
            ss << ", ";
        }
        ss << it->toString();
    }

    ss << ". Possible return sorts: ";
    first = true;
    for (auto it : retSorts) {
        if (first) {
            first = false;
        } else {
            ss << ", ";
        }
        ss << it->toString();
    }
    return ss.str();
}

string buildQuantTermDiffSort(shared_ptr<Term> term, string wrongSort, string rightSort,
                              int rowLeft, int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "Quantified term '";
    string termstr = term->toString();
    if (termstr.length() > 50) {
        ss << string(termstr, 0, 50) << "[...]";
    } else {
        ss << termstr;
    }
    ss << "' (" << rowLeft << ":" << colLeft << " - "
    << rowRight << ":" << colRight
    << ") is of type " << wrongSort << ", not " << rightSort;
    return ss.str();
}

string buildPatternMismatchMsg(string sort, string pattern) {
    stringstream ss;
    ss << "Cannot match term of sort " << sort
    << " with pattern " << pattern;
    return ss.str();
}

string buildCasesMismatchMsg(vector<shared_ptr<Sort>> caseSorts) {
    stringstream ss;
    ss << "Cases have different sorts:";
    for(auto caseSort : caseSorts) {
        ss << " " << caseSort->toString();
    }
    return ss.str();
}

void SortednessChecker::TermSorter::visit(shared_ptr<SimpleIdentifier> node) {
    shared_ptr<VarInfo> varInfo = termSorterInfo->stack->getVarInfo(node->toString());
    if (varInfo) {
        ret = varInfo->sort;
    } else {
        vector<shared_ptr<FunInfo>> infos = termSorterInfo->stack->getFunInfo(node->toString());
        vector<shared_ptr<Sort>> possibleSorts;
        for (auto it : infos) {
            if (it->signature.size() == 1 && it->params.empty())
                possibleSorts.push_back(it->signature[0]);
        }

        if (possibleSorts.size() == 1) {
            ret = possibleSorts[0];
        } else if (possibleSorts.empty()) {
            termSorterInfo->checker->addError(buildUnknownConstMsg(node->toString()), node);
        } else {
            termSorterInfo->checker->addError(buildMultipleSortsConstMsg(node->toString(), possibleSorts), node);
        }
    }
}

void SortednessChecker::TermSorter::visit(shared_ptr<QualifiedIdentifier> node) {
    vector<shared_ptr<FunInfo>> infos = termSorterInfo->stack->getFunInfo(node->getIdentifier()->toString());
    vector<shared_ptr<Sort>> retSorts;
    for (auto it : infos) {
        if (it->signature.size() == 1 && it->params.empty())
            retSorts.push_back(it->signature[0]);
    }

    shared_ptr<Sort> expanded = termSorterInfo->stack->expand(node->getSort());

    if (retSorts.size() == 1 && retSorts[0]->toString() == expanded->toString()) {
        ret = retSorts[0];
    } else {
        if (retSorts.empty()) {
            termSorterInfo->checker->addError(buildUnknownConstMsg(node->getIdentifier()->toString()), node);
        } else {
            termSorterInfo->checker->addError(buildWrongSortConstMsg(node->getIdentifier()->toString(),
                                                          expanded, retSorts), node);
        }
    }
}

void SortednessChecker::TermSorter::visit(shared_ptr<DecimalLiteral> node) {
    vector<shared_ptr<FunInfo>> infos = termSorterInfo->stack->getFunInfo(MSCONST_DECIMAL);
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        if (infos.empty()) {
            termSorterInfo->checker->addError(buildNoSortLiteralMsg(MSCONST_DECIMAL_REF), node);
        } else {
            vector<shared_ptr<Sort>> possibleSorts;
            for (auto it : infos) {
                if (it->signature.size() == 1 && it->params.empty())
                    possibleSorts.push_back(it->signature[0]);
            }
            termSorterInfo->checker->addError(buildMultipleSortsLiteralMsg(MSCONST_DECIMAL_REF, possibleSorts), node);
        }
    }
}

void SortednessChecker::TermSorter::visit(shared_ptr<NumeralLiteral> node) {
    vector<shared_ptr<FunInfo>> infos = termSorterInfo->stack->getFunInfo(MSCONST_NUMERAL);
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        if (infos.empty()) {
            termSorterInfo->checker->addError(buildNoSortLiteralMsg(MSCONST_NUMERAL_REF), node);
        } else {
            vector<shared_ptr<Sort>> possibleSorts;
            for (auto it : infos) {
                if (it->signature.size() == 1 && it->params.empty())
                    possibleSorts.push_back(it->signature[0]);
            }
            termSorterInfo->checker->addError(buildMultipleSortsLiteralMsg(MSCONST_NUMERAL_REF, possibleSorts), node);
        }
    }
}

void SortednessChecker::TermSorter::visit(shared_ptr<StringLiteral> node) {
    vector<shared_ptr<FunInfo>> infos = termSorterInfo->stack->getFunInfo(MSCONST_STRING);
    if (infos.size() == 1) {
        if (infos[0]->signature.size() == 1) {
            ret = infos[0]->signature[0];
        }
    } else {
        if (infos.empty()) {
            termSorterInfo->checker->addError(buildNoSortLiteralMsg(MSCONST_STRING_REF), node);
        } else {
            vector<shared_ptr<Sort>> possibleSorts;
            for (auto it : infos) {
                if (it->signature.size() == 1 && it->params.empty())
                    possibleSorts.push_back(it->signature[0]);
            }
            termSorterInfo->checker->addError(buildMultipleSortsLiteralMsg(MSCONST_STRING_REF, possibleSorts), node);
        }
    }
}

void SortednessChecker::TermSorter::visit(shared_ptr<QualifiedTerm> node) {
    vector<shared_ptr<Sort>> argSorts;
    for (vector<shared_ptr<Term>>::iterator it = node->getTerms().begin();
            it != node->getTerms().end(); it++) {
        shared_ptr<Sort> result = wrappedVisit(*it);
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
        name = qid->getIdentifier()->toString();
        retExpanded = termSorterInfo->stack->expand(qid->getSort());
    }

    vector<shared_ptr<FunInfo>> infos = termSorterInfo->stack->getFunInfo(name);
    vector<shared_ptr<Sort>> retSorts;


    for (auto it : infos) {
        vector<shared_ptr<Sort>> funSig;
        if(argSorts.size() >= 2) {
            if (it->assocL) {
                funSig.push_back(it->signature[0]);
                for (int i = 0; i < argSorts.size() - 1; i++) {
                    funSig.push_back(it->signature[1]);
                }
                funSig.push_back(it->signature[2]);
            } else if (it->assocR) {
                for (int i = 0; i < argSorts.size() - 1; i++) {
                    funSig.push_back(it->signature[0]);
                }
                funSig.push_back(it->signature[1]);
                funSig.push_back(it->signature[2]);
            } else if (it->chainable || it->pairwise) {
                for (int i = 0; i < argSorts.size(); i++) {
                    funSig.push_back(it->signature[0]);
                }
                funSig.push_back(it->signature[2]);
            } else {
                funSig.insert(funSig.begin(), it->signature.begin(), it->signature.end());
            }
        } else {
            funSig.insert(funSig.begin(), it->signature.begin(), it->signature.end());
        }

        if (argSorts.size() == funSig.size() - 1) {
            bool fits = true;
            if (it->params.empty()) {
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
                for (auto p : it->params) {
                    pnames.push_back(p->toString());
                }
                unordered_map<string, shared_ptr<Sort>> mapping;

                for (unsigned long i = 0; i < funSig.size() - 1; i++) {
                    fits = fits && getParamMapping(pnames, mapping, funSig[i], argSorts[i]);
                }

                if (fits && mapping.size() == it->params.size()) {
                    shared_ptr<Sort> retSort = funSig[funSig.size() - 1];
                    retSort = termSorterInfo->stack->replace(retSort, mapping);
                    string retSortString = retSort->toString();
                    if (id) {
                        retSorts.push_back(retSort);
                    } else {
                        if (retSortString == termSorterInfo->stack->expand(qid->getSort())->toString()) {
                            ret = retSort;
                            return;
                        }
                    }
                }
            }
        }
    }

    if (id) {
        if (retSorts.size() == 1) {
            ret = retSorts[0];
        } else if (retSorts.empty()) {
            termSorterInfo->checker->addError(buildNoDeclFunMsg(name, argSorts), node);
        } else {
            termSorterInfo->checker->addError(buildMultipleDeclFunMsg(name, argSorts, retSorts), node);
        }
    } else {
        termSorterInfo->checker->addError(buildNoDeclFunMsg(name, argSorts, retExpanded), node);
    }
}

void SortednessChecker::TermSorter::visit(shared_ptr<LetTerm> node) {
    termSorterInfo->stack->push();

    vector<shared_ptr<VarBinding>>& bindings = node->getBindings();
    for (auto it : bindings) {
        shared_ptr<Sort> result = wrappedVisit(it->getTerm());
        if (result) {
            termSorterInfo->stack->tryAdd(make_shared<VarInfo>(it->getSymbol()->toString(), result, node));
        } else {
            return;
        }
    }

    shared_ptr<Sort> result = wrappedVisit(node->getTerm());
    if (result) {
        ret = result;
    }

    termSorterInfo->stack->pop();
}

void SortednessChecker::TermSorter::visit(shared_ptr<ForallTerm> node) {
    termSorterInfo->stack->push();

    vector<shared_ptr<SortedVariable>>& bindings = node->getBindings();
    for (auto it : bindings) {
        termSorterInfo->stack->tryAdd(make_shared<VarInfo>(it->getSymbol()->toString(),
                                                termSorterInfo->stack->expand(it->getSort()), node));
    }

    shared_ptr<Sort> result = wrappedVisit(node->getTerm());
    if (result) {
        string resstr = result->toString();
        if (resstr == SORT_BOOL) {
            ret = result;
        } else {
            termSorterInfo->checker->addError(buildQuantTermDiffSort(node->getTerm(), resstr, SORT_BOOL,
                                                          node->getTerm()->getRowLeft(),
                                                          node->getTerm()->getColLeft(),
                                                          node->getTerm()->getRowRight(),
                                                          node->getTerm()->getColRight()), node);
        }
    }

    termSorterInfo->stack->pop();
}

void SortednessChecker::TermSorter::visit(shared_ptr<ExistsTerm> node) {
    termSorterInfo->stack->push();

    vector<shared_ptr<SortedVariable>>& bindings = node->getBindings();
    for (auto it : bindings) {
        termSorterInfo->stack->tryAdd(make_shared<VarInfo>(it->getSymbol()->toString(),
                                                termSorterInfo->stack->expand(it->getSort()), node));
    }

    shared_ptr<Sort> result = wrappedVisit(node->getTerm());
    if (result) {
        string resstr = result->toString();
        if (resstr == SORT_BOOL) {
            ret = result;
        } else {
            termSorterInfo->checker->addError(buildQuantTermDiffSort(node->getTerm(), resstr, SORT_BOOL,
                                                          node->getTerm()->getRowLeft(),
                                                          node->getTerm()->getColLeft(),
                                                          node->getTerm()->getRowRight(),
                                                          node->getTerm()->getColRight()), node);
        }
    }

    termSorterInfo->stack->pop();
}

void SortednessChecker::TermSorter::visit(shared_ptr<MatchTerm> node) {
    shared_ptr<Sort> termSort = wrappedVisit(node->getTerm());
    vector<shared_ptr<Sort>> caseSorts;

    if (termSort) {
        shared_ptr<SortednessCheckError> err;
        string termSortStr = termSort->toString();

        for (vector<shared_ptr<MatchCase>>::iterator it = node->getCases().begin();
                it != node->getCases().end(); it++) {
            shared_ptr<Pattern> pattern = (*it)->getPattern();

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
                shared_ptr<Symbol> scons = dynamic_pointer_cast<Symbol>(cons);
                shared_ptr<QualifiedConstructor> qcons = dynamic_pointer_cast<QualifiedConstructor>(cons);

                if (scons)
                    caseId = scons->toString();
                else
                    caseId = qcons->getSymbol()->toString();
            }

            // Get known information about functions with the name caseId
            vector<shared_ptr<FunInfo>> funInfos = termSorterInfo->stack->getFunInfo(caseId);
            vector<shared_ptr<FunInfo>> matchingInfos;
            vector<unordered_map<string, shared_ptr<Sort>>> matchingMappings;

            for (auto info : funInfos) {
                shared_ptr<Sort> retSort = info->signature[info->signature.size() - 1];
                string retSortStr = retSort->toString();

                // If info is about a parametric function, map sort parameters to real sorts
                vector<string> pnames;
                unordered_map<string, shared_ptr<Sort>> mapping;
                bool mapped = true;

                if (!info->params.empty()) {
                    for (auto p : info->params) {
                        pnames.push_back(p->toString());
                    }
                    mapped = getParamMapping(pnames, mapping, retSort, termSort);
                }

                // Check if current function info fits
                if (spattern || cpattern) {
                    // Return sort mismatch in case of qualified constructor
                    if (cpattern && cpattern->getSort()->toString() != termSortStr) {
                        err = termSorterInfo->checker->addError(
                                buildPatternMismatchMsg(termSortStr, pattern->toString()), node, err);
                        continue;
                    }

                    // If return sorts were mapped correctly
                    if (mapped && info->params.size() == mapping.size()) {
                        matchingInfos.push_back(info);
                        matchingMappings.push_back(mapping);
                    }
                } else if (qpattern) {
                    // Return sort mismatch in case of qualified constructor
                    if (qcons && qcons->getSort()->toString() != termSortStr) {
                        err = termSorterInfo->checker->addError(
                                buildPatternMismatchMsg(termSortStr, pattern->toString()), node, err);
                        continue;
                    }

                    // If return sorts were mapped correctly
                    // and there are as many arguments to the fuction as there are symbols in the pattern
                    if (mapped && info->params.size() == mapping.size()
                        && qpattern->getSymbols().size() == info->signature.size() - 1) {
                        matchingInfos.push_back(info);
                        matchingMappings.push_back(mapping);
                    }
                }
            }

            if (matchingInfos.empty()) {
                if (spattern && it + 1 == node->getCases().end()) {
                    // If it's not a function, try to interpret it as a variable
                    termSorterInfo->stack->push();
                    termSorterInfo->stack->tryAdd(make_shared<VarInfo>(caseId, termSort, *it));
                    shared_ptr<Sort> caseSort = wrappedVisit((*it)->getTerm());
                    if(caseSort) {
                        caseSorts.push_back(caseSort);
                    }
                    termSorterInfo->stack->pop();
                } else if (spattern || cpattern) {
                    err = termSorterInfo->checker->addError(buildNoDeclFunMsg(caseId, termSort), node, err);
                } else if (qpattern) {
                    err = termSorterInfo->checker->addError(
                            buildNoDeclFunMsg(caseId, qpattern->getSymbols().size(), termSort), node, err);
                }
            } else if (matchingInfos.size() > 1) {
                if (qpattern) {
                    err = termSorterInfo->checker->addError(
                            buildMultipleDeclFunMsg(caseId, qpattern->getSymbols().size(), termSort), node, err);
                }
            } else {
                shared_ptr<FunInfo> match = matchingInfos[0];
                if(qpattern) {
                    termSorterInfo->stack->push();
                    for(unsigned long i = 0; i < match->signature.size() - 1; i++) {
                        shared_ptr<Sort> paramSort = termSorterInfo->stack->replace(match->signature[i], matchingMappings[0]);
                        termSorterInfo->stack->tryAdd(make_shared<VarInfo>(qpattern->getSymbols()[i]->toString(), paramSort, *it));
                    }
                }

                shared_ptr<Sort> caseSort = wrappedVisit((*it)->getTerm());
                if(caseSort) {
                    caseSorts.push_back(caseSort);
                }

                if(qpattern) {
                    termSorterInfo->stack->pop();
                }
            }
        }

        if(caseSorts.size() == node->getCases().size()) {
            string case1 = caseSorts[0]->toString();
            bool equalCases = true;
            for(unsigned long i = 1; i < caseSorts.size(); i++) {
                if(caseSorts[1]->toString() != case1) {
                    err = termSorterInfo->checker->addError(buildCasesMismatchMsg(caseSorts), node, err);
                    equalCases = false;
                    break;
                }
            }
            if(equalCases)
                ret = caseSorts[0];
        }
    }
}

void SortednessChecker::TermSorter::visit(shared_ptr<AnnotatedTerm> node) {
    visit0(node->getTerm());
}


bool SortednessChecker::TermSorter::getParamMapping(vector<string>& params,
                                                    unordered_map<string, shared_ptr<Sort>>& mapping,
                                                    shared_ptr<Sort> sort1,
                                                    shared_ptr<Sort> sort2) {
    if (!sort1 || !sort2)
        return false;

    string sort1Name = sort1->getIdentifier()->toString();
    bool isParam = find(params.begin(), params.end(), sort1Name) != params.end();

    if (isParam) {
        if(mapping[sort1Name]) {
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