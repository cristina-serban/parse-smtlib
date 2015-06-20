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
    cout << ast->toString() << endl;
    SyntaxChecker *chk = new SyntaxChecker();
    cout << chk->run(ast.get()) << endl;
    cout << chk->getErrors();
    return 0;
}
