#ifndef PARSE_SMTLIB_SMT_PARSER_H
#define PARSE_SMTLIB_SMT_PARSER_H

#include <memory>
#include <string>
#include "../ast/ast_abstract.h"

namespace smtlib {
    class Parser {
    private:
        std::shared_ptr<ast::AstNode> ast;
        std::string filename;
    public:
        std::shared_ptr<smtlib::ast::AstNode> parse(std::string filename);

        bool checkSyntax();

        bool checkSortedness();

        void setAst(smtlib::ast::AstNode * ast);

        void reportError(unsigned int lineLeft, unsigned int colLeft,
                         unsigned int lineRight, unsigned int colRight, const char *msg);
    };
}

#endif //PARSE_SMTLIB_SMT_PARSER_H
