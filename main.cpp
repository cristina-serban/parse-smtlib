#include <iostream>
#include <memory>
#include "smtlib/parser/smt_parser.h"
#include "smtlib/ast/ast_abstract.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

int main() {
    Parser * parser = new Parser;
    shared_ptr<AstNode> ast = parser->parse("test.smt");
    cout << ast->toString();
    return 0;
}
