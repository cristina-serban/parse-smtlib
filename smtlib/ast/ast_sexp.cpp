#include "ast_sexp.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

CompSExpression::CompSExpression(vector<shared_ptr<SExpression>>& exprs) {
    this->exprs.insert(this->exprs.end(), exprs.begin(), exprs.end());
}

void CompSExpression::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string CompSExpression::toString() {
    stringstream ss;
    ss << "(";
    for (auto exprIt = exprs.begin(); exprIt != exprs.end(); exprIt++) {
        if(exprIt != exprs.begin())
            ss << " ";
        ss << (*exprIt)->toString();
    }
    ss <<")";
    return ss.str();
}