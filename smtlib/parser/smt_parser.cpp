#include "smt_parser.h"
#include "../util/logger.h"
#include "../visitor/ast_syntax_checker.h"
#include "../visitor/ast_sortedness_checker.h"
#include "../../parser/smtlib-glue.h"

#include <iostream>

extern "C" {
    extern FILE* yyin;
}

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

shared_ptr<AstNode> Parser::parse(std::string filename) {
    yyin = fopen(filename.c_str(), "r");
    if(yyin) {
        this->filename = make_shared<string>(filename.c_str());
        yyparse(this);
        fclose(yyin);
    } else {
        stringstream ss;
        ss << "Unable to open file '" << filename << "'";
        Logger::error("Parser::parse()", ss.str().c_str());
    }
    return ast;
}

std::shared_ptr<std::string> Parser::getFilename() {
    return filename;
}

void Parser::setAst(shared_ptr<AstNode> ast) {
    if(ast) {
        this->ast = ast;
    }
}

std::shared_ptr<ast::AstNode> Parser::getAst() {
    return ast;
}

void Parser::reportError(unsigned int lineLeft, unsigned int colLeft,
                 unsigned int lineRight, unsigned int colRight, const char* msg) {
    Logger::parsingError(lineLeft, colLeft, lineRight, colRight, filename->c_str(), msg);
}