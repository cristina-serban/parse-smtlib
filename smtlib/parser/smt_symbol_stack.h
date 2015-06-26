#ifndef PARSE_SMTLIB_SMT_SYMBOL_STACK_H
#define PARSE_SMTLIB_SMT_SYMBOL_STACK_H

#include "smt_symbol_table.h"
#include <memory>
#include <vector>

namespace smtlib {
    class SymbolStack {
    private:
        std::vector<std::shared_ptr<SymbolTable>> stack;
    public:
        SymbolStack();

        std::shared_ptr<SymbolTable> getTopLevel();

        std::vector<std::shared_ptr<SymbolTable>> &getStack();

        bool pushLevel();
        bool popLevel();

        /*bool equal(std::shared_ptr<ast::Sort> sort1, std::shared_ptr<ast::Sort> sort2);*/

        std::shared_ptr<SortInfo> getSortInfo(std::string name);
        std::vector<std::shared_ptr<FunInfo>> getFunInfo(std::string name);
    };
}

#endif //PARSE_SMTLIB_SMT_SYMBOL_STACK_H
