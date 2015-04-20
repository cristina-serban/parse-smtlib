#include "smt_s_expr.h"

using namespace std;
using namespace smt;

CompSExpression::CompSExpression(vector<shared_ptr<ISExpression>> &exprs) {
    for(vector<shared_ptr<ISExpression>>::iterator it = exprs.begin(); it != exprs.end(); it++) {
        this->exprs.push_back(*it);
    }
}

vector<shared_ptr<ISExpression>> &CompSExpression::getExpressions() {
    return exprs;
}
