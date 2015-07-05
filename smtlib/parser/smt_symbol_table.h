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
                std::shared_ptr<VarInfo>> vars;

    public:
        std::unordered_map<std::string, std::shared_ptr<SortInfo>>& getSorts();
        std::unordered_map<std::string, std::vector<std::shared_ptr<FunInfo>>>& getFuns();
        std::unordered_map<std::string, std::shared_ptr<VarInfo>>& getVars();

        std::shared_ptr<SortInfo> getSortInfo(std::string name);
        std::vector<std::shared_ptr<FunInfo>> getFunInfo(std::string name);
        std::shared_ptr<VarInfo> getVarInfo(std::string name);

        bool add(std::shared_ptr<SortInfo> info);
        bool add(std::shared_ptr<FunInfo> info);
        bool add(std::shared_ptr<VarInfo> info);

        void reset();
    };
}

#endif //PARSE_SMTLIB_SMT_SYMBOL_TABLE_H