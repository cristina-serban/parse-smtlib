#ifndef PARSE_SMTLIB_SMT_SYMBOL_UTIL_H
#define PARSE_SMTLIB_SMT_SYMBOL_UTIL_H

#include "../ast/ast_basic.h"
#include "../ast/ast_term.h"

#include <memory>
#include <string>

namespace smtlib {
    struct SortDefInfo {
        std::vector<std::shared_ptr<ast::Symbol>> params;
        std::shared_ptr<ast::Sort> sort;

        SortDefInfo(std::vector<std::shared_ptr<ast::Symbol>> &params,
                    std::shared_ptr<ast::Sort> sort) {
            this->params.insert(this->params.begin(), params.begin(), params.end());
            this->sort = sort;
        }
    };

    struct SortInfo {
        std::string name;
        unsigned long arity;
        std::shared_ptr<SortDefInfo> definition;
        std::vector<std::shared_ptr<ast::Attribute>> attributes;
        std::shared_ptr<ast::AstNode> source;

        SortInfo(std::string name, unsigned long arity,
                 std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->arity = arity;
            this->source = source;
        }

        SortInfo(std::string name, unsigned long arity,
                 std::vector<std::shared_ptr<ast::Attribute>> &attributes,
                 std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->arity = arity;
            this->source = source;
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }

        SortInfo(std::string name, unsigned long arity,
                 std::vector<std::shared_ptr<ast::Symbol>> &params,
                 std::shared_ptr<ast::Sort> sort,
                 std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->arity = arity;
            this->source = source;
            this->definition = std::make_shared<SortDefInfo>(params, sort);
        }

        SortInfo(std::string name, unsigned long arity,
                 std::vector<std::shared_ptr<ast::Symbol>> &params,
                 std::shared_ptr<ast::Sort> sort,
                 std::vector<std::shared_ptr<ast::Attribute>> &attributes,
                 std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->arity = arity;
            this->source = source;
            this->definition = std::make_shared<SortDefInfo>(params, sort);
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }
    };

    struct FunInfo {
        std::string name;
        std::vector<std::shared_ptr<ast::Sort>> signature;
        std::vector<std::shared_ptr<ast::Symbol>> params;
        std::shared_ptr<ast::Term> body;
        std::shared_ptr<ast::AstNode> source;
        std::vector<std::shared_ptr<ast::Attribute>> attributes;

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>> &signature,
                std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
            this->params.insert(this->params.begin(), params.begin(), params.end());
            this->body = body;
            this->source = source;
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>> &signature,
                std::shared_ptr<ast::Term> body,
                std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
            this->body = body;
            this->source = source;
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>> &signature,
                std::vector<std::shared_ptr<ast::Symbol>> &params,
                std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
            this->params.insert(this->params.begin(), params.begin(), params.end());
            this->source = source;
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>> &signature,
                std::vector<std::shared_ptr<ast::Symbol>> &params,
                std::shared_ptr<ast::Term> body,
                std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
            this->params.insert(this->params.begin(), params.begin(), params.end());
            this->body = body;
            this->source = source;
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>> &signature,
                std::vector<std::shared_ptr<ast::Attribute>> &attributes,
                std::shared_ptr<ast::AstNode> source){
            this->name = name;
            this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
            this->params.insert(this->params.begin(), params.begin(), params.end());
            this->body = body;
            this->source = source;
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>> &signature,
                std::shared_ptr<ast::Term> body,
                std::vector<std::shared_ptr<ast::Attribute>> &attributes,
                std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
            this->body = body;
            this->source = source;
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>> &signature,
                std::vector<std::shared_ptr<ast::Symbol>> &params,
                std::vector<std::shared_ptr<ast::Attribute>> &attributes,
                std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
            this->params.insert(this->params.begin(), params.begin(), params.end());
            this->source = source;
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>> &signature,
                std::vector<std::shared_ptr<ast::Symbol>> &params,
                std::shared_ptr<ast::Term> body,
                std::vector<std::shared_ptr<ast::Attribute>> &attributes,
                std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
            this->params.insert(this->params.begin(), params.begin(), params.end());
            this->body = body;
            this->source = source;
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }
    };

    struct VariableInfo {
        std::string name;
        std::shared_ptr<ast::Sort> sort;
        std::shared_ptr<ast::Term> term;

        VariableInfo(std::string name,
                     std::shared_ptr<ast::Sort> sort) {
            this->name = name;
            this->sort = sort;
        }

        VariableInfo(std::string name,
                     std::shared_ptr<ast::Sort> sort,
                     std::shared_ptr<ast::Term> term) {
            this->name = name;
            this->sort = sort;
            this->term = term;
        }
    };
}
#endif //PARSE_SMTLIB_SMT_SYMBOL_UTIL_H