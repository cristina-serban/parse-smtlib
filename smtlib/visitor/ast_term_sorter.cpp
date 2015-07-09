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

void SortednessChecker::TermSorter::visit(shared_ptr<SimpleIdentifier> node) {
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

void SortednessChecker::TermSorter::visit(shared_ptr<QualifiedIdentifier> node) {
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

void SortednessChecker::TermSorter::visit(shared_ptr<DecimalLiteral> node) {
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

void SortednessChecker::TermSorter::visit(shared_ptr<NumeralLiteral> node) {
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

void SortednessChecker::TermSorter::visit(shared_ptr<StringLiteral> node) {
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

void SortednessChecker::TermSorter::visit(shared_ptr<QualifiedTerm> node) {
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
                ss << string(termstr, 0, 50) << "[...]";
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

    shared_ptr<SimpleIdentifier> id = dynamic_pointer_cast<SimpleIdentifier>(node->getIdentifier());
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
                    fits = fits && getParamMapping(pnames, mapping, it->signature[i], argSorts[i]);
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
        } else if (retSorts.empty()) {
            stringstream ss;
            ss << "No known declaration for function '" << name << "' with parameters list (";
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
            arg->checker->addError(ss.str(), node);
        } else {
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
            arg->checker->addError(ss.str(), node);
        }
    } else {
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
        ss << ") and return sort " << retExpanded->toString();
        arg->checker->addError(ss.str(), node);
    }
}

void SortednessChecker::TermSorter::visit(shared_ptr<LetTerm> node) {
    arg->stack->push();

    vector<shared_ptr<VarBinding>>& bindings = node->getBindings();
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
            ss << string(termstr, 0, 50) << "[...]";
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

void SortednessChecker::TermSorter::visit(shared_ptr<ForallTerm> node) {
    arg->stack->push();

    vector<shared_ptr<SortedVariable>>& bindings = node->getBindings();
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
                ss << string(termstr, 0, 50) << "[...]";
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
            ss << string(termstr, 0, 50) << "[...]";
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

void SortednessChecker::TermSorter::visit(shared_ptr<ExistsTerm> node) {
    arg->stack->push();

    vector<shared_ptr<SortedVariable>>& bindings = node->getBindings();
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
                ss << string(termstr, 0, 50) << "[...]";
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
            ss << string(termstr, 0, 50) << "[...]";
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

void SortednessChecker::TermSorter::visit(shared_ptr<MatchTerm> node) {
    TermSorter sorter;
    shared_ptr<Sort> termSort = sorter.run(arg, node->getTerm());
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
            vector<shared_ptr<FunInfo>> funInfos = arg->stack->getFunInfo(caseId);
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
                        stringstream ss;
                        ss << "Cannot match term of sort " << termSortStr
                        << " with pattern " << pattern->toString();
                        err = arg->checker->addError(ss.str(), node, err);
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
                        stringstream ss;
                        ss << "Cannot match term of sort " << termSortStr
                        << " with pattern " << pattern->toString();
                        err = arg->checker->addError(ss.str(), node, err);
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
                    arg->stack->push();
                    arg->stack->tryAdd(make_shared<VarInfo>(caseId, termSort, *it));
                    shared_ptr<Sort> caseSort = sorter.run(arg, (*it)->getTerm());
                    if(caseSort) {
                        caseSorts.push_back(caseSort);
                    } else {
                        stringstream ss;
                        ss << "Term '";
                        string termstr = (*it)->getTerm()->toString();
                        if (termstr.length() > 50) {
                            ss << string(termstr, 0, 50) << "[...]";
                        } else {
                            ss << termstr;
                        }
                        ss << "' (" << node->getTerm()->getRowLeft() << ":" << node->getTerm()->getColLeft() << " - "
                        << node->getTerm()->getRowRight() << ":" << node->getTerm()->getColRight()
                        << ") is not well-sorted";
                        err = arg->checker->addError(ss.str(), node, err);
                    }
                    arg->stack->pop();
                } else if (spattern || cpattern) {
                    stringstream ss;
                    ss << "No known declaration for function '" << caseId << "' with return sort " << termSortStr;
                    err = arg->checker->addError(ss.str(), node, err);
                } else if (qpattern) {
                    stringstream ss;
                    ss << "No known declaration for function '" << caseId << "' with "
                    << qpattern->getSymbols().size() << " arguments and return sort " << termSortStr;
                    err = arg->checker->addError(ss.str(), node, err);
                }
            } else if (matchingInfos.size() > 1) {
                if (qpattern) {
                    stringstream ss;
                    ss << "Multiple possible declarations for function '" << caseId << "' with "
                    << qpattern->getSymbols().size() << " arguments and return sort " << termSortStr;
                    err = arg->checker->addError(ss.str(), node, err);
                }
            } else {
                shared_ptr<FunInfo> match = matchingInfos[0];
                if(qpattern) {
                    arg->stack->push();
                    for(unsigned long i = 0; i < match->signature.size() - 1; i++) {
                        shared_ptr<Sort> paramSort = arg->stack->replace(match->signature[i], matchingMappings[0]);
                        arg->stack->tryAdd(make_shared<VarInfo>(qpattern->getSymbols()[i]->toString(), termSort, *it));
                    }
                }

                shared_ptr<Sort> caseSort = sorter.run(arg, (*it)->getTerm());
                if(caseSort) {
                    caseSorts.push_back(caseSort);
                } else {
                    stringstream ss;
                    ss << "Term '";
                    string termstr = (*it)->getTerm()->toString();
                    if (termstr.length() > 50) {
                        ss << string(termstr, 0, 50) << "[...]";
                    } else {
                        ss << termstr;
                    }
                    ss << "' (" << node->getTerm()->getRowLeft() << ":" << node->getTerm()->getColLeft() << " - "
                    << node->getTerm()->getRowRight() << ":" << node->getTerm()->getColRight()
                    << ") is not well-sorted";
                    err = arg->checker->addError(ss.str(), node, err);
                }

                if(qpattern) {
                    arg->stack->pop();
                }
            }
        }

        if(caseSorts.size() == node->getCases().size()) {
            string case1 = caseSorts[0]->toString();
            for(unsigned long i = 1; i < caseSorts.size(); i++) {
                if(caseSorts[1]->toString() != case1) {
                    stringstream ss;
                    ss << "Cases have different sorts:";
                    for(auto caseSort : caseSorts) {
                        ss << " " << caseSort->toString();
                    }
                    err = arg->checker->addError(ss.str(), node, err);
                    break;
                }
            }
        }
    } else {
        stringstream ss;
        ss << "Term '";
        string termstr = node->getTerm()->toString();
        if (termstr.length() > 50) {
            ss << string(termstr, 0, 50) << "[...]";
        } else {
            ss << termstr;
        }
        ss << "' (" << node->getTerm()->getRowLeft() << ":" << node->getTerm()->getColLeft() << " - "
        << node->getTerm()->getRowRight() << ":" << node->getTerm()->getColRight()
        << ") is not well-sorted";
        arg->checker->addError(ss.str(), node);
    }
}

void SortednessChecker::TermSorter::visit(shared_ptr<AnnotatedTerm> node) {
    node->getTerm()->accept(this);
}


bool SortednessChecker::TermSorter::getParamMapping(vector<string>& params,
                                                    unordered_map<string, shared_ptr<Sort>>& mapping,
                                                    shared_ptr<Sort> sort1,
                                                    shared_ptr<Sort> sort2) {
    if (!sort1 || !sort2)
        return false;

    if (sort1->getArgs().size() != sort2->getArgs().size()) {
        return false;
    } else if (sort1->getArgs().empty()) {
        string sort1Name = sort1->getIdentifier()->toString();
        bool isParam = find(params.begin(), params.end(), sort1Name) != params.end();

        if (isParam) {
            mapping[sort1Name] = sort2;
            return true;
        } else {
            return sort1Name == sort2->getIdentifier()->toString();
        }

    } else {
        string sort1Name = sort1->getIdentifier()->toString();
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