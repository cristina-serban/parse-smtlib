#ifndef PARSE_SMTLIB_SMT_PARSER_H
#define PARSE_SMTLIB_SMT_PARSER_H

#include "../ast/ast_abstract.h"

#include <memory>
#include <string>

namespace smtlib {
    class Parser {
    private:
        std::shared_ptr<ast::AstNode> ast;
        std::shared_ptr<std::string> filename;
    public:
        std::shared_ptr<ast::AstNode> parse(std::string filename);

        bool checkSyntax();

        bool checkSortedness();

        const std::shared_ptr<std::string> getFilename() const;
        std::shared_ptr<std::string> getFilename();

        void setAst(smtlib::ast::AstNode *ast);

        std::shared_ptr<ast::AstNode> getAst();

        void reportError(unsigned int lineLeft, unsigned int colLeft,
                         unsigned int lineRight, unsigned int colRight, const char *msg);
    };
}

#endif //PARSE_SMTLIB_SMT_PARSER_H
