#ifndef PARSE_SMTLIB_SMT_SYMBOL_UTIL_H
#define PARSE_SMTLIB_SMT_SYMBOL_UTIL_H

#include "../ast/ast_basic.h"
#include "../ast/ast_term.h"

#include <memory>
#include <string>

namespace smtlib {
    class SymbolInfo {
    public:
        std::string name;
        std::shared_ptr<ast::AstNode> source;

        virtual ~SymbolInfo();
    };

    class SortDefInfo {
    public:
        std::vector<std::shared_ptr<ast::Symbol>> params;
        std::shared_ptr<ast::Sort> sort;

        SortDefInfo(std::vector<std::shared_ptr<ast::Symbol>>& params,
                    std::shared_ptr<ast::Sort> sort) {
            this->params.insert(this->params.begin(), params.begin(), params.end());
            this->sort = sort;
        }
    };

    class SortInfo : public SymbolInfo {
    public:
        unsigned long arity;
        std::shared_ptr<SortDefInfo> definition;
        std::vector<std::shared_ptr<ast::Attribute>> attributes;

        SortInfo(std::string name, unsigned long arity,
                 std::shared_ptr<ast::AstNode> source) : arity(arity) {
            this->name = name;
            this->source = source;
        }

        SortInfo(std::string name, unsigned long arity,
                 std::vector<std::shared_ptr<ast::Attribute>>& attributes,
                 std::shared_ptr<ast::AstNode> source) : arity(arity) {
            this->name = name;
            this->source = source;
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }

        SortInfo(std::string name, unsigned long arity,
                 std::vector<std::shared_ptr<ast::Symbol>>& params,
                 std::shared_ptr<ast::Sort> sort,
                 std::shared_ptr<ast::AstNode> source) : arity(arity)  {
            this->name = name;
            this->source = source;
            this->definition = std::make_shared<SortDefInfo>(params, sort);
        }

        SortInfo(std::string name, unsigned long arity,
                 std::vector<std::shared_ptr<ast::Symbol>>& params,
                 std::shared_ptr<ast::Sort> sort,
                 std::vector<std::shared_ptr<ast::Attribute>>& attributes,
                 std::shared_ptr<ast::AstNode> source) : arity(arity)  {
            this->name = name;
            this->source = source;
            this->definition = std::make_shared<SortDefInfo>(params, sort);
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }
    };

    class FunInfo : public SymbolInfo {
    private:
        inline void init(std::string name,
                         std::vector<std::shared_ptr<ast::Sort>>& signature,
                         std::shared_ptr<ast::AstNode> source) {
            this->name = name;
            this->signature.insert(this->signature.begin(), signature.begin(), signature.end());
            this->source = source;
            assocL = false;
            assocR = false;
            chainable = false;
            pairwise = false;
        }

    public:
        std::vector<std::shared_ptr<ast::Sort>> signature;
        std::vector<std::shared_ptr<ast::Symbol>> params;
        std::shared_ptr<ast::Term> body;
        std::vector<std::shared_ptr<ast::Attribute>> attributes;

        bool assocR;
        bool assocL;
        bool chainable;
        bool pairwise;

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>>& signature,
                std::shared_ptr<ast::AstNode> source) {
            init(name, signature, source);
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>>& signature,
                std::shared_ptr<ast::Term> body,
                std::shared_ptr<ast::AstNode> source) : body(body) {
            init(name, signature, source);
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>>& signature,
                std::vector<std::shared_ptr<ast::Symbol>>& params,
                std::shared_ptr<ast::AstNode> source) {
            init(name, signature, source);
            this->params.insert(this->params.begin(), params.begin(), params.end());
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>>& signature,
                std::vector<std::shared_ptr<ast::Symbol>>& params,
                std::shared_ptr<ast::Term> body,
                std::shared_ptr<ast::AstNode> source) : body(body) {
            init(name, signature, source);
            this->params.insert(this->params.begin(), params.begin(), params.end());
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>>& signature,
                std::vector<std::shared_ptr<ast::Attribute>>& attributes,
                std::shared_ptr<ast::AstNode> source) {
            init(name, signature, source);
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>>& signature,
                std::shared_ptr<ast::Term> body,
                std::vector<std::shared_ptr<ast::Attribute>>& attributes,
                std::shared_ptr<ast::AstNode> source) : body(body) {
            init(name, signature, source);
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>>& signature,
                std::vector<std::shared_ptr<ast::Symbol>>& params,
                std::vector<std::shared_ptr<ast::Attribute>>& attributes,
                std::shared_ptr<ast::AstNode> source) {
            init(name, signature, source);
            this->params.insert(this->params.begin(), params.begin(), params.end());
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }

        FunInfo(std::string name,
                std::vector<std::shared_ptr<ast::Sort>>& signature,
                std::vector<std::shared_ptr<ast::Symbol>>& params,
                std::shared_ptr<ast::Term> body,
                std::vector<std::shared_ptr<ast::Attribute>>& attributes,
                std::shared_ptr<ast::AstNode> source) : body(body) {
            init(name, signature, source);
            this->params.insert(this->params.begin(), params.begin(), params.end());
            this->attributes.insert(this->attributes.begin(), attributes.begin(), attributes.end());
        }
    };

    class VarInfo : public SymbolInfo {
    public:
        std::shared_ptr<ast::Sort> sort;
        std::shared_ptr<ast::Term> term;

        VarInfo(std::string name,
                std::shared_ptr<ast::Sort> sort,
                std::shared_ptr<ast::AstNode> source) : sort(sort) {
            this->name = name;
            this->source = source;
        }

        VarInfo(std::string name,
                std::shared_ptr<ast::Sort> sort,
                std::shared_ptr<ast::Term> term,
                std::shared_ptr<ast::AstNode> source) : sort(sort), term(term) {
            this->name = name;
            this->source = source;
        }
    };
}
#endif //PARSE_SMTLIB_SMT_SYMBOL_UTIL_H