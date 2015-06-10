#include <sstream>
#include "ast_sexp.h"

using namespace std;
using namespace smtlib::ast;

CompSExpression::CompSExpression(const vector<shared_ptr<SExpression>> &exprs) {
    this->exprs.insert(this->exprs.end(), exprs.begin(), exprs.end());
}

vector<shared_ptr<SExpression>> &CompSExpression::getExpressions() {
    return exprs;
}

void CompSExpression::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string CompSExpression::toString() {
    stringstream ss;
    ss << "( ";
    for(vector<shared_ptr<SExpression>>::iterator it = exprs.begin(); it != exprs.end(); it++) {
        ss << (*it)->toString() << " ";
    }
    ss <<")";
    return ss.str();
}