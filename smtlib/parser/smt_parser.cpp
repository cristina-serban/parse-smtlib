#include <iostream>
#include "smt_parser.h"
#include "../util/smt_logger.h"
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
        this->filename = filename;
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

void Parser::reportError(unsigned int lineL, unsigned int colL,
                 unsigned int lineR, unsigned int colR, const char *msg) {
    Logger::ErrorParsing(lineL, colL, lineR, colR, filename.c_str(), msg);
}