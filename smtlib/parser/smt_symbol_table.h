#ifndef PARSE_SMTLIB_SMT_SYMBOL_TABLE_H
#define PARSE_SMTLIB_SMT_SYMBOL_TABLE_H

#include "../ast/ast_basic.h"
#include "../ast/ast_symbol_decl.h"

#include <string>
#include <unordered_map>

namespace smtlib {
    class SymbolTable {
    private:
        std::unordered_map<std::string,
                std::shared_ptr<ast::SortSymbolDeclaration>> sortDeclarations;

        std::unordered_map<std::string,
                std::pair<std::vector<std::shared_ptr<ast::Symbol>>,
                        std::shared_ptr<ast::Sort>>> sortDefinitions;

        std::unordered_map<std::string,
                std::vector<std::shared_ptr<ast::FunSymbolDeclaration>>> funs;

        std::unordered_map<std::string,
                std::shared_ptr<ast::SortedVariable>> vars;

        bool equalSignatures(std::vector<std::shared_ptr<ast::Sort>> &sig1,
                             std::vector<std::shared_ptr<ast::Sort>> &sig2);

        bool equalParamSignatures(std::vector<std::shared_ptr<ast::Symbol>> &params1,
                                  std::vector<std::shared_ptr<ast::Sort>> &sig1,
                                  std::vector<std::shared_ptr<ast::Symbol>> &params,
                                  std::vector<std::shared_ptr<ast::Sort>> &sig2);

        bool equalParamSorts(std::vector<std::shared_ptr<ast::Symbol>> &params1,
                             std::shared_ptr<ast::Sort> sort1,
                             std::vector<std::shared_ptr<ast::Symbol>> &params2,
                             std::shared_ptr<ast::Sort> sort2,
                             std::unordered_map<std::string, std::string> &mapping);

    public:
        const std::unordered_map<std::string,
                std::shared_ptr<ast::SortSymbolDeclaration>> &getSortDeclarations() const;

        std::unordered_map<std::string,
                std::shared_ptr<ast::SortSymbolDeclaration>> &getSortDeclarations();

        const std::unordered_map<std::string,
                std::pair<std::vector<std::shared_ptr<ast::Symbol>>,
                        std::shared_ptr<ast::Sort>>> &getSortDefinitions() const;

        std::unordered_map<std::string,
                std::pair<std::vector<std::shared_ptr<ast::Symbol>>,
                        std::shared_ptr<ast::Sort>>> &getSortDefinitions();

        const std::unordered_map<std::string,
                std::vector<std::shared_ptr<ast::FunSymbolDeclaration>>> &getFuns() const;

        std::unordered_map<std::string,
                std::vector<std::shared_ptr<ast::FunSymbolDeclaration>>> &getFuns();

        const std::unordered_map<std::string,
                std::shared_ptr<ast::SortedVariable>> &getVars() const;
        std::unordered_map<std::string,
                std::shared_ptr<ast::SortedVariable>> &getVars();

        bool addSort(std::shared_ptr<ast::SortSymbolDeclaration> node);
        bool addSort(std::shared_ptr<ast::DeclareSortCommand> node);
        bool addSort(std::shared_ptr<ast::DefineSortCommand> node);

        bool addFun(std::shared_ptr<ast::SpecConstFunDeclaration> node);
        bool addFun(std::shared_ptr<ast::MetaSpecConstFunDeclaration> node);
        bool addFun(std::shared_ptr<ast::IdentifierFunDeclaration> node);
        bool addFun(std::shared_ptr<ast::ParametricFunDeclaration> node);
        bool addFun(std::shared_ptr<ast::DeclareConstCommand> node);
        bool addFun(std::shared_ptr<ast::DeclareFunCommand> node);
        bool addFun(std::shared_ptr<ast::DefineFunCommand> node);
        bool addFun(std::shared_ptr<ast::DefineFunRecCommand> node);
        bool addFun(std::shared_ptr<ast::DefineFunsRecCommand> node);

        bool addVariable(std::shared_ptr<ast::SortedVariable> node);
    };
}

#endif //PARSE_SMTLIB_SMT_SYMBOL_TABLE_H
