#ifndef PARSE_SMTLIB_SMT_PARSER_H
#define PARSE_SMTLIB_SMT_PARSER_H

#include <memory>
#include <string>
#include "../ast/smt_abstract.h"

namespace smt {
    class SmtParser {
    private:
        std::shared_ptr<ast::SmtAstNode> ast;
    public:
        std::shared_ptr<smt::ast::SmtAstNode> parse(std::string filename);

        void setAst(smt::ast::SmtAstNode* ast);
    };
}

#endif //PARSE_SMTLIB_SMT_PARSER_H
