#include <sstream>
#include "smt_s_expr.h"

using namespace std;
using namespace smtlib::ast;

CompSExpression::CompSExpression(const vector<shared_ptr<ISExpression>> &exprs) {
    this->exprs.insert(this->exprs.end(), exprs.begin(), exprs.end());
}

vector<shared_ptr<ISExpression>> &CompSExpression::getExpressions() {
    return exprs;
}

string CompSExpression::toString() {
    stringstream ss;
    ss << "( ";
    for(vector<shared_ptr<ISExpression>>::iterator it = exprs.begin(); it != exprs.end(); it++) {
        ss << (*it)->toString() << " ";
    }
    ss <<")";
    return ss.str();
}