#include "smt_parser.h"
#include "../util/smt_logger.h"
#include "../visitor/ast_syntax_checker.h"
#include "../../parser/smtlib-glue.h"

#include <iostream>
#include <sstream>

extern "C" {
    extern FILE* yyin;
}

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

shared_ptr<AstNode> Parser::parse(std::string filename) {
    yyin = fopen(filename.c_str(), "r");
    if(yyin) {
        shared_ptr<string> shared = make_shared<string>(filename.c_str());
        yyparse(this);
        fclose(yyin);
    }
    return ast;
}

const std::shared_ptr<std::string> Parser::getFilename() const {
    return filename;
}

std::shared_ptr<std::string> Parser::getFilename() {
    return filename;
}

bool Parser::checkSyntax() {
    if(ast) {
        SyntaxChecker *chk = new SyntaxChecker();
        if(chk->run(ast.get())) {
            return true;
        } else {
            Logger::syntaxError("Parser::checkSyntax()", filename->c_str(), chk->getErrors().c_str());
            return false;
        }
    } else {
        Logger::warning("Parser::checkSyntax()", "Attempting to check an empty abstract syntax tree");
        return false;
    }
}

void Parser::setAst(AstNode * ast) {
    if(ast) {
        this->ast = shared_ptr<AstNode>(ast);
    }
}

std::shared_ptr<ast::AstNode> Parser::getAst() {
    return ast;
}

void Parser::reportError(unsigned int lineLeft, unsigned int colLeft,
                 unsigned int lineRight, unsigned int colRight, const char *msg) {
    Logger::parsingError(lineLeft, colLeft, lineRight, colRight, filename->c_str(), msg);
}