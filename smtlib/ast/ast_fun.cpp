#include "ast_fun.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================ FunctionDeclaration =============================== */

FunctionDeclaration::FunctionDeclaration(shared_ptr<Symbol> symbol,
                                         vector<shared_ptr<SortedVariable>>& params,
                                         shared_ptr<Sort> sort)
        : symbol(symbol), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

void FunctionDeclaration::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string FunctionDeclaration::toString() {
    stringstream ss;
    ss << symbol->toString() << " (";

    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        if(paramIt != params.begin())
            ss << " ";
        ss << "(" << (*paramIt)->toString() << ")";
    }

    ss << ") " << sort->toString();

    return ss.str();
}

/* ================================ FunctionDefinition ================================ */

FunctionDefinition::FunctionDefinition(shared_ptr<Symbol> symbol,
                                       vector<shared_ptr<SortedVariable>>& params,
                                       shared_ptr<Sort> sort,
                                       shared_ptr<Term> body)
        : body(body) {
    signature = make_shared<FunctionDeclaration>(symbol, params, sort);
}

void FunctionDefinition::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string FunctionDefinition::toString() {
    stringstream ss;
    ss << signature->toString() << " " << body->toString();
    return ss.str();
}