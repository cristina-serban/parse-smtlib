#include "ast_command.h"
#include <sstream>

using namespace std;
using namespace smtlib::ast;

/* ================================== AssertCommand =================================== */

void AssertCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string AssertCommand::toString() {
    stringstream ss;
    ss << "(assert " << term->toString() << ")";
    return ss.str();
}

/* ================================= CheckSatCommand ================================== */

void CheckSatCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string CheckSatCommand::toString() {
    return "(check-sat)";
}

/* =============================== CheckSatAssumCommand =============================== */

CheckSatAssumCommand::CheckSatAssumCommand(vector<shared_ptr<PropLiteral>>& assumptions) {
    this->assumptions.insert(this->assumptions.end(), assumptions.begin(), assumptions.end());
}

void CheckSatAssumCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string CheckSatAssumCommand::toString() {
    stringstream ss;
    ss << "(check-sat-assuming (";

    for (vector<shared_ptr<PropLiteral>>::iterator it = assumptions.begin(); it != assumptions.end(); it++) {
        if(it != assumptions.begin())
            ss << " ";
        ss << (*it)->toString();
    }

    ss << "))";

    return ss.str();
}

/* =============================== DeclareConstCommand ================================ */

void DeclareConstCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string DeclareConstCommand::toString() {
    stringstream ss;
    ss << "(declare-const " << symbol->toString() << " " << sort->toString() << ")";
    return ss.str();
}

/* ============================== DeclareDatatypeCommand ============================== */
void DeclareDatatypeCommand::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DeclareDatatypeCommand::toString() {
    stringstream ss;
    ss << "(declare-datatype " << symbol->toString() << " " << declaration->toString() << ")";
    return ss.str();
}

/* ============================= DeclareDatatypesCommand ============================== */
DeclareDatatypesCommand::DeclareDatatypesCommand(vector<shared_ptr<SortDeclaration>>& sorts,
                                                 vector<shared_ptr<DatatypeDeclaration>>& declarations) {
    this->sorts.insert(this->sorts.begin(), sorts.begin(), sorts.end());
    this->declarations.insert(this->declarations.begin(), declarations.begin(), declarations.end());
}

void DeclareDatatypesCommand::accept(AstVisitor0* visitor) {
    visitor->visit(shared_from_this());
}

string DeclareDatatypesCommand::toString() {
    stringstream ss;
    ss << "( declare-datatypes (";

    bool first = true;
    for(auto it : sorts) {
        if(first)
            first = false;
        else
            ss << " ";
        ss << it->toString();
    }

    ss << ") (";

    first = true;
    for(auto it : declarations) {
        if(first)
            first = false;
        else
            ss << " ";
        ss << it->toString();
    }

    return ss.str();
}
/* =============================== DeclareFunCommand ================================ */

DeclareFunCommand::DeclareFunCommand(shared_ptr<Symbol> symbol,
                                     vector<shared_ptr<Sort>>& params,
                                     shared_ptr<Sort> sort)
        : symbol(symbol), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

void DeclareFunCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string DeclareFunCommand::toString() {
    stringstream ss;
    ss << "(declare-fun " << symbol->toString() << " (";

    for (vector<shared_ptr<Sort>>::iterator it = params.begin(); it != params.end(); it++) {
        if(it != params.begin())
            ss << " ";
        ss << (*it)->toString();
    }

    ss << ") " << sort->toString() << ")";

    return ss.str();
}

/* =============================== DeclareSortCommand ================================ */

void DeclareSortCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string DeclareSortCommand::toString() {
    stringstream ss;
    ss << "(declare-sort " << symbol->toString() << " " << arity->toString() << ")";
    return ss.str();
}

/* ================================= DefineFunCommand ================================= */

DefineFunCommand::DefineFunCommand(shared_ptr<Symbol> symbol,
                                   vector<shared_ptr<SortedVariable>>& params,
                                   shared_ptr<Sort> sort,
                                   shared_ptr<Term> body) {
    definition = make_shared<FunctionDefinition>(symbol, params, sort, body);
}

void DefineFunCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string DefineFunCommand::toString() {
    stringstream ss;
    ss << "(define-fun " << definition->toString() << ")";
    return ss.str();
}

/* ================================ DefineFunRecCommand =============================== */

DefineFunRecCommand::DefineFunRecCommand(shared_ptr<Symbol> symbol,
                                         vector<shared_ptr<SortedVariable>>& params,
                                         shared_ptr<Sort> sort,
                                         shared_ptr<Term> body) {
    definition = make_shared<FunctionDefinition>(symbol, params, sort, body);
}

void DefineFunRecCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string DefineFunRecCommand::toString() {
    stringstream ss;
    ss << "(define-fun-rec " << definition->toString() << ")";
    return ss.str();
}

/* =============================== DefineFunsRecCommand =============================== */

DefineFunsRecCommand::DefineFunsRecCommand(
        vector<shared_ptr<FunctionDeclaration>>& declarations,
        vector<shared_ptr<Term>>& bodies) {
    this->declarations.insert(this->declarations.end(), declarations.begin(), declarations.end());
    this->bodies.insert(this->bodies.end(), bodies.begin(), bodies.end());
}

void DefineFunsRecCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string DefineFunsRecCommand::toString() {
    stringstream ss;
    ss << "(define-funs-rec (";
    for (vector<shared_ptr<FunctionDeclaration>>::iterator it = declarations.begin();
         it != declarations.end(); it++) {
        if(it != declarations.begin())
            ss << " ";
        ss << "(" << (*it)->toString() << ")";
    }

    ss << ") (";
    for (vector<shared_ptr<Term>>::iterator it = bodies.begin(); it != bodies.end(); it++) {
        if(it != bodies.begin())
            ss << " ";
        ss << "(" << (*it)->toString() << ")";
    }

    ss << "))";
    return ss.str();
}

/* ================================ DefineSortCommand ================================= */

DefineSortCommand::DefineSortCommand(shared_ptr<Symbol> symbol,
                                     vector<shared_ptr<Symbol>>& params,
                                     shared_ptr<Sort> sort)
        : symbol(symbol), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

void DefineSortCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string DefineSortCommand::toString() {
    stringstream ss;
    ss << "(define-sort " << symbol->toString() << " (";
    for (vector<shared_ptr<Symbol>>::iterator it = params.begin(); it != params.end(); it++) {
        if(it != params.begin())
            ss << " ";
        ss << (*it)->toString();
    }

    ss << ") " << sort->toString() << ")";
    return ss.str();
}

/* =================================== EchoCommand ==================================== */

void EchoCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string EchoCommand::toString() {
    stringstream ss;
    ss << "(echo " << message << ")";
    return ss.str();
}

/* =================================== ExitCommand ==================================== */

void ExitCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string ExitCommand::toString() {
    return "(exit)";
}

/* ================================ GetAssertsCommand ================================= */

void GetAssertsCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetAssertsCommand::toString() {
    return "(get-assertions)";
}

/* ================================ GetAssignsCommand ================================= */

void GetAssignsCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetAssignsCommand::toString() {
    return "(get-assignments)";
}

/* ================================== GetInfoCommand ================================== */

void GetInfoCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetInfoCommand::toString() {
    stringstream ss;
    ss << "(get-info " << flag->toString() << ")";
    return ss.str();
}

/* ================================= GetModelCommand ================================== */

void GetModelCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetModelCommand::toString() {
    return "(get-model)";
}

/* ================================= GetOptionCommand ================================= */

void GetOptionCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetOptionCommand::toString() {
    stringstream ss;
    ss << "(get-option " << option->toString() << ")";
    return ss.str();
}

/* ================================= GetProofCommand ================================== */

void GetProofCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetProofCommand::toString() {
    return "(get-proof)";
}

/* ============================== GetUnsatAssumsCommand =============================== */

void GetUnsatAssumsCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetUnsatAssumsCommand::toString() {
    return "(get-unsat-assumptions)";
}

/* =============================== GetUnsatCoreCommand ================================ */

void GetUnsatCoreCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetUnsatCoreCommand::toString() {
    return "(get-unsat-core)";
}

/* ================================= GetValueCommand ================================== */

GetValueCommand::GetValueCommand(vector<shared_ptr<Term>>& terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

void GetValueCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string GetValueCommand::toString() {
    stringstream ss;
    ss << "(get-value (";

    for(vector<shared_ptr<Term>>::iterator it = terms.begin(); it != terms.end(); it++) {
        if(it != terms.begin())
            ss << " ";
        ss << (*it)->toString();
    }

    ss << "))";
    return ss.str();
}

/* =================================== PopCommand ==================================== */

void PopCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string PopCommand::toString() {
    stringstream ss;
    ss << "(pop " << numeral->toString() << ")";
    return ss.str();
}

/* =================================== PushCommand ==================================== */

void PushCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string PushCommand::toString() {
    stringstream ss;
    ss << "(push " << numeral->toString() << ")";
    return ss.str();
}

/* =================================== ResetCommand =================================== */

void ResetCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string ResetCommand::toString() {
    return "(reset)";
}

/* =============================== ResetAssertsCommand ================================ */

void ResetAssertsCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string ResetAssertsCommand::toString() {
    return "(reset-assertions)";
}

/* ================================== SetInfoCommand ================================== */

void SetInfoCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string SetInfoCommand::toString() {
    stringstream ss;
    ss << "(set-info " << info->getKeyword()->toString()
       << " " << info->getValue()->toString() << ")";
    return ss.str();
}

/* ================================= SetLogicCommand ================================== */

void SetLogicCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string SetLogicCommand::toString() {
    stringstream ss;
    ss << "(set-logic " << logic->toString() << ")";
    return ss.str();
}

/* ================================= SetOptionCommand ================================= */

void SetOptionCommand::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
} 

string SetOptionCommand::toString() {
    stringstream ss;
    ss << "(set-option " << option->getKeyword()->toString()
       << " " << option->getValue()->toString() << ")";
    return ss.str();
}