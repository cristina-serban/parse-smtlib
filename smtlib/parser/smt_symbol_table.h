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

        bool addSort(std::shared_ptr<SortInfo> info);

        bool addFun(std::shared_ptr<FunInfo> info);

        bool addVariable(std::shared_ptr<VariableInfo> node);
    };
}

#endif //PARSE_SMTLIB_SMT_SYMBOL_TABLE_H