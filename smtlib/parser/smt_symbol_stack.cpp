#include "smt_symbol_stack.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

SymbolStack::SymbolStack() {
    push();
}

shared_ptr<SymbolTable> SymbolStack::getTopLevel() {
    return stack[stack.size() - 1];
}

vector<shared_ptr<SymbolTable>>& SymbolStack::getStack() {
    return stack;
}

bool SymbolStack::push() {
    unsigned long size = stack.size();
    stack.push_back(make_shared<SymbolTable>());
    return (stack.size() == size + 1);
}

bool SymbolStack::push(unsigned long levels) {
    unsigned long size = stack.size();
    for (int i = 0; i < levels; i++)
        stack.push_back(make_shared<SymbolTable>());
    return (stack.size() == size + levels);
}

bool SymbolStack::pop() {
    if (stack.size() <= 1) {
        return false;
    } else {
        unsigned long size = stack.size();
        stack.erase(stack.begin() + (stack.size() - 1));
        return (stack.size() == size - 1);
    }
}

bool SymbolStack::pop(unsigned long levels) {
    if (stack.size() <= 1 + levels || levels == 0) {
        return false;
    } else {
        unsigned long size = stack.size();
        stack.erase(stack.begin() + (stack.size() - levels), stack.begin() + (stack.size() - 1));
        return (stack.size() == size - 1);
    }
}

void SymbolStack::reset() {
    pop(stack.size() - 1);
    getTopLevel()->reset();
}

shared_ptr<SortInfo> SymbolStack::getSortInfo(string name) {
    shared_ptr<SortInfo> null;
    for (vector<shared_ptr<SymbolTable>>::iterator it = stack.begin(); it != stack.end(); it++) {
        shared_ptr<SortInfo> info = (*it)->getSortInfo(name);
        if (info)
            return info;
    }
    return null;
}

vector<shared_ptr<FunInfo>> SymbolStack::getFunInfo(string name) {
    vector<shared_ptr<FunInfo>> result;
    for (vector<shared_ptr<SymbolTable>>::iterator it = stack.begin(); it != stack.end(); it++) {
        vector<shared_ptr<FunInfo>> infos = (*it)->getFunInfo(name);
        result.insert(result.end(), infos.begin(), infos.end());
    }
    return result;
}

shared_ptr<VarInfo> SymbolStack::getVarInfo(string name) {
    shared_ptr<VarInfo> null;
    for (vector<shared_ptr<SymbolTable>>::iterator it = stack.begin(); it != stack.end(); it++) {
        shared_ptr<VarInfo> info = (*it)->getVarInfo(name);
        if (info)
            return info;
    }
    return null;
}

shared_ptr<SortInfo> SymbolStack::findDuplicate(shared_ptr<SortInfo> info) {
    shared_ptr<SortInfo> null;
    for (vector<shared_ptr<SymbolTable>>::iterator it = stack.begin(); it != stack.end(); it++) {
        shared_ptr<SortInfo> dup = (*it)->getSortInfo(info->name);
        if (dup)
            return dup;
    }
    return null;
}

shared_ptr<FunInfo> SymbolStack::findDuplicate(shared_ptr<FunInfo> info) {
    shared_ptr<FunInfo> null;
    vector<shared_ptr<FunInfo>> known = getFunInfo(info->name);
    for (vector<shared_ptr<FunInfo>>::iterator it = known.begin(); it != known.end(); it++) {
        if (info->params.size() == 0 && (*it)->params.size() == 0) {
            if (equal(info->signature, (*it)->signature)) {
                return (*it);
            }
        } else {
            if (equal(info->params, info->signature,
                      (*it)->params, (*it)->signature)) {
                return (*it);
            }
        }
    }
    return null;
}

shared_ptr<VarInfo> SymbolStack::findDuplicate(shared_ptr<VarInfo> info) {
    return getTopLevel()->getVarInfo(info->name);
}

shared_ptr<Sort> SymbolStack::replace(shared_ptr<Sort> sort,
                                      unordered_map<string, shared_ptr<Sort>>& mapping) {
    if (mapping.empty())
        return sort;

    if (!sort->hasArgs()) {
        if (mapping.find(sort->toString()) != mapping.end())
            return mapping[sort->toString()];
        else
            return sort;
    } else {
        vector<shared_ptr<Sort>> newargs;
        bool changed = false;
        for (vector<shared_ptr<Sort>>::iterator it = sort->getArgs().begin();
             it != sort->getArgs().end(); it++) {
            shared_ptr<Sort> result = replace(*it, mapping);

            newargs.push_back(result);
            if (result.get() != (*it).get())
                changed = true;
        }

        if (changed) {
            return make_shared<Sort>(sort->getIdentifier(), newargs);
        } else {
            return sort;
        }
    }
}

shared_ptr<Sort> SymbolStack::expand(shared_ptr<Sort> sort) {
    if (!sort)
        return sort;

    shared_ptr<Sort> null;

    shared_ptr<SortInfo> info = getSortInfo(sort->getIdentifier()->toString());
    if (!sort->hasArgs()) {
        if (info && info->definition) {
            if (info->definition->params.empty()) {
                shared_ptr<Sort> newsort = make_shared<Sort>(info->definition->sort->getIdentifier(),
                                                             info->definition->sort->getArgs());
                newsort->setRowLeft(sort->getRowLeft());
                newsort->setColLeft(sort->getColLeft());
                newsort->setRowRight(sort->getRowRight());
                newsort->setColRight(sort->getColRight());
                newsort->setFilename(sort->getFilename());

                return newsort;
            } else {
                return null;
            }
        } else {
            return sort;
        }
    } else {
        if (info && info->definition) {
            if (info->definition->params.size() == sort->getArgs().size()) {
                unordered_map<string, shared_ptr<Sort>> mapping;
                for (int i = 0; i < info->definition->params.size(); i++) {
                    mapping[info->definition->params[i]->toString()] = sort->getArgs()[i];
                }

                shared_ptr<Sort> newsort = replace(info->definition->sort, mapping);
                newsort = expand(newsort);
                newsort->setRowLeft(sort->getRowLeft());
                newsort->setColLeft(sort->getColLeft());
                newsort->setRowRight(sort->getRowRight());
                newsort->setColRight(sort->getColRight());
                newsort->setFilename(sort->getFilename());

                return newsort;
            } else {
                return null;
            }
        } else {
            if (info && info->arity != sort->getArgs().size())
                return null;

            vector<shared_ptr<Sort>> newargs;
            bool changed = false;
            for (vector<shared_ptr<Sort>>::iterator it = sort->getArgs().begin();
                 it != sort->getArgs().end(); it++) {
                shared_ptr<Sort> result = expand(*it);
                if (!result)
                    return null;

                newargs.push_back(result);
                if (result.get() != (*it).get())
                    changed = true;
            }

            if (changed) {
                shared_ptr<Sort> newsort = make_shared<Sort>(sort->getIdentifier(), newargs);
                newsort->setRowLeft(sort->getRowLeft());
                newsort->setColLeft(sort->getColLeft());
                newsort->setRowRight(sort->getRowRight());
                newsort->setColRight(sort->getColRight());
                newsort->setFilename(sort->getFilename());

                return newsort;
            } else {
                return sort;
            }
        }
    }
}

bool SymbolStack::equal(shared_ptr<Sort> sort1,
                        shared_ptr<Sort> sort2) {
    return sort1->toString() == sort2->toString();
}

bool SymbolStack::equal(vector<shared_ptr<Symbol>>& params1,
                        shared_ptr<Sort> sort1,
                        vector<shared_ptr<Symbol>>& params2,
                        shared_ptr<Sort> sort2,
                        unordered_map<string, string>& mapping) {
    if (sort1->getArgs().size() != sort2->getArgs().size())
        return false;

    if (sort1->getArgs().size() == 0) {
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
            return equal(sort1, sort2);
        }
    } else {
        if (sort1->getIdentifier()->toString() != sort2->getIdentifier()->toString())
            return false;

        for (unsigned long k = 0; k < sort1->getArgs().size(); k++) {
            if (!equal(params1, sort1->getArgs()[k], params2, sort2->getArgs()[k], mapping))
                return false;
        }

        return true;
    }
}

bool SymbolStack::equal(vector<shared_ptr<Sort>>& signature1,
                        vector<shared_ptr<Sort>>& signature2) {
    if (signature1.size() != signature2.size())
        return false;

    for (unsigned long i = 0; i < signature1.size(); i++) {
        if (!equal(signature1[i], signature2[i]))
            return false;
    }

    return true;
}

bool SymbolStack::equal(vector<shared_ptr<Symbol>>& params1,
                        vector<shared_ptr<Sort>>& signature1,
                        vector<shared_ptr<Symbol>>& params2,
                        vector<shared_ptr<Sort>>& signature2) {
    if (params1.size() != params2.size() || signature1.size() != signature2.size())
        return false;

    unordered_map<string, string> mapping;
    for (unsigned long i = 0; i < signature1.size(); i++) {
        shared_ptr<Sort> sort1 = signature1[i];
        shared_ptr<Sort> sort2 = signature2[i];

        if (!equal(params1, sort1, params2, sort2, mapping))
            return false;
    }

    return mapping.size() == params1.size();
}

shared_ptr<SortInfo> SymbolStack::tryAdd(shared_ptr<SortInfo> info) {
    shared_ptr<SortInfo> dup = findDuplicate(info);
    if (!dup)
        getTopLevel()->add(info);
    return dup;
}

shared_ptr<FunInfo> SymbolStack::tryAdd(shared_ptr<FunInfo> info) {
    shared_ptr<FunInfo> dup = findDuplicate(info);
    if (!dup)
        getTopLevel()->add(info);
    return dup;
}

std::shared_ptr<VarInfo> SymbolStack::tryAdd(shared_ptr<VarInfo> info) {
    shared_ptr<VarInfo> dup = findDuplicate(info);
    if (!dup)
        getTopLevel()->add(info);
    return dup;
}