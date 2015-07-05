#ifndef PARSE_SMTLIB_SMT_SYMBOL_STACK_H
#define PARSE_SMTLIB_SMT_SYMBOL_STACK_H

#include "smt_symbol_table.h"
#include <memory>
#include <vector>

namespace smtlib {
    class SymbolStack {
    private:
        std::vector<std::shared_ptr<SymbolTable>> stack;

        bool equal(std::shared_ptr<ast::Sort> sort1,
                   std::shared_ptr<ast::Sort> sort2);

        bool equal(std::vector<std::shared_ptr<ast::Sort>>& signature1,
                   std::vector<std::shared_ptr<ast::Sort>>& signature2);

        bool equal(std::vector<std::shared_ptr<ast::Symbol>>& params1,
                   std::vector<std::shared_ptr<ast::Sort>>& signature1,
                   std::vector<std::shared_ptr<ast::Symbol>>& params2,
                   std::vector<std::shared_ptr<ast::Sort>>& signature2);

        bool equal(std::vector<std::shared_ptr<ast::Symbol>>& params1,
                   std::shared_ptr<ast::Sort> sort1,
                   std::vector<std::shared_ptr<ast::Symbol>>& params2,
                   std::shared_ptr<ast::Sort> sort2,
                   std::unordered_map<std::string, std::string> &mapping);

        std::shared_ptr<ast::Sort> replace(std::shared_ptr<ast::Sort>,
                                           std::unordered_map<std::string, std::shared_ptr<ast::Sort>>& mapping);
    public:
        SymbolStack();

        std::shared_ptr<SymbolTable> getTopLevel();

        std::vector<std::shared_ptr<SymbolTable>>& getStack();

        bool push();
        bool push(unsigned long levels);

        bool pop();
        bool pop(unsigned long levels);

        void reset();

        std::shared_ptr<SortInfo> getSortInfo(std::string name);
        std::vector<std::shared_ptr<FunInfo>> getFunInfo(std::string name);
        std::shared_ptr<VarInfo> getVarInfo(std::string name);

        std::shared_ptr<SortInfo> findDuplicate(std::shared_ptr<SortInfo> info);
        std::shared_ptr<FunInfo> findDuplicate(std::shared_ptr<FunInfo> info);
        std::shared_ptr<VarInfo> findDuplicate(std::shared_ptr<VarInfo> info);

        std::shared_ptr<ast::Sort> expand(std::shared_ptr<ast::Sort>);

        std::shared_ptr<SortInfo> tryAdd(std::shared_ptr<SortInfo> info);
        std::shared_ptr<FunInfo> tryAdd(std::shared_ptr<FunInfo> info);
        std::shared_ptr<VarInfo> tryAdd(std::shared_ptr<VarInfo> info);
    };
}

#endif //PARSE_SMTLIB_SMT_SYMBOL_STACK_H
