#include <iostream>
#include <memory>
#include <parser/smt_parser.h>
#include <ast/ast_abstract.h>
#include <visitor/ast_syntax_checker.h>

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

int main() {
    Parser *parser = new Parser;
    shared_ptr<AstNode> ast = parser->parse("test.smt");
    cout << ast->toString();
    AstSyntaxChecker *chk = new AstSyntaxChecker();
    cout << chk->run(ast.get());
    return 0;
}
