#ifndef PARSE_SMTLIB_SMT_SYMBOL_TABLE_H
#define PARSE_SMTLIB_SMT_SYMBOL_TABLE_H

#include "smt_symbol_util.h"

#include <memory>
#include <string>
#include <unordered_map>

namespace smtlib {
    class SymbolTable {
    private:
        std::unordered_map<std::string, std::shared_ptr<SortInfo>> sorts;

        std::unordered_map<std::string,
                std::vector<std::shared_ptr<FunInfo>>> funs;

        std::unordered_map<std::string,
                std::shared_ptr<VariableInfo>> vars;

    public:
        std::unordered_map<std::string, std::shared_ptr<SortInfo>> &getSorts();
        std::unordered_map<std::string, std::vector<std::shared_ptr<FunInfo>>> &getFuns();
        std::unordered_map<std::string, std::shared_ptr<VariableInfo>> &getVars();

        std::shared_ptr<SortInfo> duplicate (std::shared_ptr<SortInfo> info);
        std::shared_ptr<FunInfo> duplicate (std::shared_ptr<FunInfo> info);
        std::shared_ptr<VariableInfo> duplicate (std::shared_ptr<VariableInfo> info);

        bool add(std::shared_ptr<SortInfo> info);
        bool add(std::shared_ptr<FunInfo> info);
        bool add(std::shared_ptr<VariableInfo> info);
    };
}

#endif //PARSE_SMTLIB_SMT_SYMBOL_TABLE_H