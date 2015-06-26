#ifndef PARSE_SMTLIB_SMT_SYMBOL_STACK_H
#define PARSE_SMTLIB_SMT_SYMBOL_STACK_H

#include "smt_symbol_table.h"
#include <memory>
#include <vector>

namespace smtlib {
    class SymbolStack {
    private:
        std::vector<std::shared_ptr<SymbolTable>> stack;

        bool equal(std::vector<std::shared_ptr<ast::Symbol>> &params1,
                   std::shared_ptr<ast::Sort> sort1,
                   std::vector<std::shared_ptr<ast::Symbol>> &params2,
                   std::shared_ptr<ast::Sort> sort2,
                   std::unordered_map<std::string, std::string> &mapping);
    public:
        SymbolStack();

        std::shared_ptr<SymbolTable> getTopLevel();

        std::vector<std::shared_ptr<SymbolTable>> &getStack();

        bool pushLevel();
        bool popLevel();

        std::shared_ptr<SortInfo> getSortInfo(std::string name);
        std::vector<std::shared_ptr<FunInfo>> getFunInfo(std::string name);

        std::shared_ptr<SortInfo> duplicate (std::shared_ptr<SortInfo> info);
        std::shared_ptr<FunInfo> duplicate (std::shared_ptr<FunInfo> info);
        std::shared_ptr<VariableInfo> duplicate (std::shared_ptr<VariableInfo> info);

        std::shared_ptr<ast::Sort> expand(std::shared_ptr<ast::Sort>);

        bool equal(std::shared_ptr<ast::Sort> sort1,
                   std::shared_ptr<ast::Sort> sort2);

        bool equal(std::vector<std::shared_ptr<ast::Sort>> &signature1,
                   std::vector<std::shared_ptr<ast::Sort>> &signature2);

        bool equal(std::vector<std::shared_ptr<ast::Symbol>> &params1,
                   std::vector<std::shared_ptr<ast::Sort>> &signature1,
                   std::vector<std::shared_ptr<ast::Symbol>> &params2,
                   std::vector<std::shared_ptr<ast::Sort>> &signature2);

        bool add(std::shared_ptr<SortInfo> info);
        bool add(std::shared_ptr<FunInfo> info);
        bool add(std::shared_ptr<VariableInfo> info);
    };
}

#endif //PARSE_SMTLIB_SMT_SYMBOL_STACK_H
