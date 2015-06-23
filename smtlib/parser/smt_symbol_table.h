#ifndef PARSE_SMTLIB_SMT_SYMBOL_TABLE_H
#define PARSE_SMTLIB_SMT_SYMBOL_TABLE_H

#include "../ast/ast_basic.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_term.h"

#include <memory>
#include <string>
#include <unordered_map>

namespace smtlib {
    struct SortDefinition {
        std::vector<std::shared_ptr<ast::Symbol>> params;
        std::shared_ptr<ast::Sort> sort;

        SortDefinition(std::vector<std::shared_ptr<ast::Symbol>> params,
                       std::shared_ptr<ast::Sort> sort) {
            this->params = params;
            this->sort = sort;
        }
    };

    struct SortInfo{
        std::shared_ptr<ast::SortSymbolDeclaration> declaration;
        std::shared_ptr<SortDefinition> definition;
        std::shared_ptr<ast::AstNode> source;

        SortInfo(std::shared_ptr<ast::SortSymbolDeclaration> declaration,
                 std::shared_ptr<ast::AstNode> source) {
            this->declaration = declaration;
            this->source = source;
        }

        SortInfo(std::shared_ptr<ast::SortSymbolDeclaration> declaration,
                 std::vector<std::shared_ptr<ast::Symbol>> parameters,
                 std::shared_ptr<ast::Sort> sort,
                 std::shared_ptr<ast::AstNode> source) {
            this->declaration = declaration;
            this->definition = std::make_shared<SortDefinition>(parameters, sort);
            this->source = source;
        }
    };

    struct FunInfo {
        std::shared_ptr<ast::FunSymbolDeclaration> declaration;
        std::shared_ptr<ast::Term> body;
        std::shared_ptr<ast::AstNode> source;

        FunInfo(std::shared_ptr<ast::FunSymbolDeclaration> declaration,
                std::shared_ptr<ast::AstNode> source) {
            this->declaration = declaration;
            this->source = source;
        }

        FunInfo(std::shared_ptr<ast::FunSymbolDeclaration> declaration,
                std::shared_ptr<ast::Term> body,
                std::shared_ptr<ast::AstNode> source) {
            this->declaration = declaration;
            this->body = body;
            this->source = source;
        }
    };

    class SymbolTable {
    private:
        std::unordered_map<std::string, std::shared_ptr<SortInfo>> sorts;

        std::unordered_map<std::string,
                std::vector<std::shared_ptr<FunInfo>>> funs;

        std::unordered_map<std::string,
                std::shared_ptr<ast::SortedVariable>> vars;

    public:
        const std::unordered_map<std::string, std::shared_ptr<SortInfo>> &getSorts() const;
        std::unordered_map<std::string, std::shared_ptr<SortInfo>> &getSorts();

        const std::unordered_map<std::string, std::vector<std::shared_ptr<FunInfo>>> &getFuns() const;
        std::unordered_map<std::string, std::vector<std::shared_ptr<FunInfo>>> &getFuns();

        const std::unordered_map<std::string, std::shared_ptr<ast::SortedVariable>> &getVars() const;
        std::unordered_map<std::string, std::shared_ptr<ast::SortedVariable>> &getVars();

        bool addSort(std::string name, std::shared_ptr<SortInfo> info);

        bool addFun(std::string name, std::shared_ptr<FunInfo> info);

        bool addVariable(std::shared_ptr<ast::SortedVariable> node);
    };
}

#endif //PARSE_SMTLIB_SMT_SYMBOL_TABLE_H