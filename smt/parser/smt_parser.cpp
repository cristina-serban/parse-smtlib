#include <iostream>
#include "smt_parser.h"
#include "../../parser/smtlib-glue.h"

extern "C" {
    extern FILE* yyin;
}

using namespace std;
using namespace smt;
using namespace smt::ast;

shared_ptr<SmtAstNode> SmtParser::parse(std::string filename) {
    yyin = fopen(filename.c_str(), "r");
    if(yyin) {
        yyparse(this);
        fclose(yyin);
    }
    return ast;
}

void SmtParser::setAst(SmtAstNode* ast) {
    if(ast) {
        this->ast = shared_ptr<SmtAstNode>(ast);
    }
}