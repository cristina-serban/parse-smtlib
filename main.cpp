#include <iostream>
#include <memory>
#include "smt_parser.h"
#include "../ast/ast_script.h"
#include "../ast/ast_abstract.h"
#include "../visitor/ast_syntax_checker.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

int main(int argc, char** argv) {
    if (argc == 2) {
        Parser* parser = new Parser;
        shared_ptr<AstNode> ast = parser->parse(argv[1]);
        parser->checkSortedness();
        return 0;
    } else {
        return 1;
    }
}
