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
        bool pushLevel();
        bool popLevel();

        const std::shared_ptr<SymbolTable> getTopLevel() const;
        std::shared_ptr<SymbolTable> getTopLevel();

        const std::vector<std::shared_ptr<SymbolTable>> &getStack() const;
        std::vector<std::shared_ptr<SymbolTable>> &getStack();
    };
}

#endif //PARSE_SMTLIB_SMT_SYMBOL_STACK_H
