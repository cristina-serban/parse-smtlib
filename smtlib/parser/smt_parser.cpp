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
        this->filename = filename;
        yyparse(this);
        fclose(yyin);
    }
    return ast;
}

bool Parser::checkSyntax() {
    if(ast) {
        SyntaxChecker *chk = new SyntaxChecker();
        if(chk->run(ast.get())) {
            return true;
        } else {
            stringstream ss;
            ss << "Syntax errors in file " + filename + ":" << endl << chk->getErrors();
            Logger::Error2("Parser::checkSyntax()", ss.str().c_str());
            return false;
        }
    } else {
        Logger::Warning("Parser::checkSyntax()", "Attempting to check an empty abstract syntax tree");
        return false;
    }
}

void Parser::setAst(AstNode * ast) {
    if(ast) {
        this->ast = shared_ptr<AstNode>(ast);
    }
}

void Parser::reportError(unsigned int lineLeft, unsigned int colLeft,
                 unsigned int lineRight, unsigned int colRight, const char *msg) {
    Logger::ParsingError(lineLeft, colLeft, lineRight, colRight, filename.c_str(), msg);
}