#include "ast_sexp.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

CompSExpression::CompSExpression(const vector<shared_ptr<SExpression>> &exprs) {
    this->exprs.insert(this->exprs.end(), exprs.begin(), exprs.end());
}

const vector<shared_ptr<SExpression>> &CompSExpression::getExpressions() const {
    return exprs;
}

vector<shared_ptr<SExpression>> &CompSExpression::getExpressions() {
    return exprs;
}

void CompSExpression::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
}

string CompSExpression::toString() const {
    stringstream ss;
    ss << "(";
    for(vector<shared_ptr<SExpression>>::const_iterator it = exprs.begin(); it != exprs.end(); it++) {
        if(it != exprs.begin())
            ss << " ";
        ss << (*it)->toString();
    }
    ss <<")";
    return ss.str();
}