#ifndef PARSE_SMTLIB_SMT_PARSER_H
#define PARSE_SMTLIB_SMT_PARSER_H

#include <memory>
#include <string>
#include "../ast/smt_abstract.h"

namespace smtlib {
    class Parser {
    private:
        std::shared_ptr<ast::AstNode> ast;
    public:
        std::shared_ptr<smtlib::ast::AstNode> parse(std::string filename);

        void setAst(smtlib::ast::AstNode * ast);
    };
}

#endif //PARSE_SMTLIB_SMT_PARSER_H
