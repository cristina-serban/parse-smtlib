#include <iostream>
#include "smt_parser.h"
#include "../../parser/smtlib-glue.h"

extern "C" {
    extern FILE* yyin;
}

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

shared_ptr<AstNode> Parser::parse(std::string filename) {
    yyin = fopen(filename.c_str(), "r");
    if(yyin) {
        yyparse(this);
        fclose(yyin);
    }
    return ast;
}

void Parser::setAst(AstNode * ast) {
    if(ast) {
        this->ast = shared_ptr<AstNode>(ast);
    }
}