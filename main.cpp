#include <iostream>
#include <memory>
#include "smt/parser/smt_parser.h"
#include "smt/ast/smt_abstract.h"

using namespace std;
using namespace smt;
using namespace smt::ast;

int main() {
    SmtParser* parser = new SmtParser;
    shared_ptr<SmtAstNode> ast = parser->parse("test.smt");
    cout << ast->toString();
    return 0;
}
