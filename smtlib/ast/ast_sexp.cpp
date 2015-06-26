#include "ast_sexp.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

CompSExpression::CompSExpression(vector<shared_ptr<SExpression>> &exprs) {
    this->exprs.insert(this->exprs.end(), exprs.begin(), exprs.end());
}

vector<shared_ptr<SExpression>> &CompSExpression::getExpressions() {
    return exprs;
}

void CompSExpression::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string CompSExpression::toString() {
    stringstream ss;
    ss << "(";
    for(vector<shared_ptr<SExpression>>::iterator it = exprs.begin(); it != exprs.end(); it++) {
        if(it != exprs.begin())
            ss << " ";
        ss << (*it)->toString();
    }
    ss <<")";
    return ss.str();
}