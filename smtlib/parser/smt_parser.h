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

        void setAst(smtlib::ast::AstNode * ast);

        void reportError(unsigned int lineL, unsigned int colL,
                         unsigned int lineR, unsigned int colR, const char *msg);
    };
}

#endif //PARSE_SMTLIB_SMT_PARSER_H
