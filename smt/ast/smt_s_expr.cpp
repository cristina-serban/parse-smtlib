#include "smt_s_expr.h"

using namespace std;
using namespace smt::ast;

CompSExpression::CompSExpression(vector<shared_ptr<ISExpression>> &exprs) {
    this->exprs.insert(this->exprs.end(), exprs.begin(), exprs.end());
}

vector<shared_ptr<ISExpression>> &CompSExpression::getExpressions() {
    return exprs;
}