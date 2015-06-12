#include <sstream>
#include "ast_command.h"

using namespace std;
using namespace smtlib::ast;

/* ================================== AssertCommand =================================== */

shared_ptr<Term> AssertCommand::getTerm() const {
    return term;
}

void AssertCommand::setTerm(shared_ptr<Term> term) {
    this->term = term;
}

void AssertCommand::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string AssertCommand::toString() {
    stringstream ss;
    ss << "( assert " << term->toString() << " )";
    return ss.str();
}

/* ================================= CheckSatCommand ================================== */

void CheckSatCommand::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string CheckSatCommand::toString() {
    return "( check-sat )";
}

/* =============================== CheckSatAssumCommand =============================== */

CheckSatAssumCommand::CheckSatAssumCommand(const vector<shared_ptr<PropLiteral>> &assumptions) {
    this->assumptions.insert(this->assumptions.end(), assumptions.begin(), assumptions.end());
}

vector<shared_ptr<PropLiteral>> &CheckSatAssumCommand::getAssumptions() {
    return assumptions;
}

void CheckSatAssumCommand::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string CheckSatAssumCommand::toString() {
    stringstream ss;
    ss << "( check-sat-assuming ( ";

    for (vector<shared_ptr<PropLiteral>>::iterator it = assumptions.begin();
         it != assumptions.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ") )";

    return ss.str();
}

/* =============================== DeclareConstCommand ================================ */

shared_ptr<Symbol> DeclareConstCommand::getSymbol() const {
    return symbol;
}

void DeclareConstCommand::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

shared_ptr<Sort> DeclareConstCommand::getSort() const {
    return sort;
}

void DeclareConstCommand::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

void DeclareConstCommand::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string DeclareConstCommand::toString() {
    stringstream ss;
    ss << "( declare-const " << symbol->toString() << " " << sort->toString() << " )";
    return ss.str();
}

/* =============================== DeclareFunCommand ================================ */

DeclareFunCommand::DeclareFunCommand(shared_ptr<Symbol> symbol,
                                     const vector<shared_ptr<Sort>> &params,
                                     shared_ptr<Sort> sort)
        : symbol(symbol), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

shared_ptr<Symbol> DeclareFunCommand::getSymbol() const {
    return symbol;
}

void DeclareFunCommand::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

vector<shared_ptr<Sort>> &DeclareFunCommand::getParams() {
    return params;
}

shared_ptr<Sort> DeclareFunCommand::getSort() const {
    return sort;
}

void DeclareFunCommand::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

void DeclareFunCommand::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string DeclareFunCommand::toString() {
    stringstream ss;
    ss << "( declare-fun " << symbol->toString() << " ( ";

    for (vector<shared_ptr<Sort>>::iterator it = params.begin(); it != params.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << " ) " << sort->toString() << " )";

    return ss.str();
}

/* =============================== DeclareSortCommand ================================ */

shared_ptr<Symbol> DeclareSortCommand::getSymbol() const {
    return symbol;
}

void DeclareSortCommand::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

shared_ptr<NumeralLiteral> DeclareSortCommand::getArity() const {
    return arity;
}

void DeclareSortCommand::setArity(shared_ptr<NumeralLiteral> arity) {
    this->arity = arity;
}

void DeclareSortCommand::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string DeclareSortCommand::toString() {
    stringstream ss;
    ss << "( declare-sort " << symbol->toString() << " " << arity->toString() << " )";
    return ss.str();
}

/* ================================= DefineFunCommand ================================= */

DefineFunCommand::DefineFunCommand(shared_ptr<FunctionDeclaration> signature,
                                   shared_ptr<Term> body) {
    definition = make_shared<FunctionDefinition>(signature, body);
}

DefineFunCommand::DefineFunCommand(shared_ptr<Symbol> symbol,
                                   const vector<shared_ptr<SortedVariable>> &params,
                                   shared_ptr<Sort> sort,
                                   shared_ptr<Term> body) {
    definition = make_shared<FunctionDefinition>(symbol, params, sort, body);
}

shared_ptr<FunctionDefinition> DefineFunCommand::getDefinition() const {
    return definition;
}

void DefineFunCommand::setDefinition(shared_ptr<FunctionDefinition> definition) {
    this->definition = definition;
}

void DefineFunCommand::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string DefineFunCommand::toString() {
    stringstream ss;
    ss << "( define-fun " << definition->toString() << " )";
    return ss.str();
}

/* ================================ DefineFunRecCommand =============================== */

DefineFunRecCommand::DefineFunRecCommand(shared_ptr<FunctionDeclaration> signature,
                                         shared_ptr<Term> body) {
    definition = make_shared<FunctionDefinition>(signature, body);
}

DefineFunRecCommand::DefineFunRecCommand(shared_ptr<Symbol> symbol,
                                         const vector<shared_ptr<SortedVariable>> &params,
                                         shared_ptr<Sort> sort,
                                         shared_ptr<Term> body) {
    definition = make_shared<FunctionDefinition>(symbol, params, sort, body);
}

shared_ptr<FunctionDefinition> DefineFunRecCommand::getDefinition() const {
    return definition;
}

void DefineFunRecCommand::setDefinition(shared_ptr<FunctionDefinition> definition) {
    this->definition = definition;
}

void DefineFunRecCommand::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string DefineFunRecCommand::toString() {
    stringstream ss;
    ss << "( define-fun-rec " << definition->toString() << " )";
    return ss.str();
}

/* =============================== DefineFunsRecCommand =============================== */

DefineFunsRecCommand::DefineFunsRecCommand(
        const std::vector<std::shared_ptr<FunctionDeclaration>> &declarations,
        const std::vector<std::shared_ptr<Term>> &bodies) {
    this->declarations.insert(this->declarations.end(), declarations.begin(), declarations.end());
    this->bodies.insert(this->bodies.end(), bodies.begin(), bodies.end());
}

std::vector<std::shared_ptr<FunctionDeclaration>> &DefineFunsRecCommand::getDeclarations() {
    return declarations;
}

std::vector<std::shared_ptr<Term>> &DefineFunsRecCommand::getBodies() {
    return bodies;
}

std::vector<std::shared_ptr<FunctionDeclaration>> DefineFunsRecCommand::getDeclarations() const {
    return declarations;
}

std::vector<std::shared_ptr<Term>> DefineFunsRecCommand::getBodies() const {
    return bodies;
}

void DefineFunsRecCommand::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string DefineFunsRecCommand::toString() {
    stringstream ss;
    ss << "( define-funs-rec ( ";
    for (vector<shared_ptr<FunctionDeclaration>>::iterator it = declarations.begin();
         it != declarations.end(); it++) {
        ss << "(" << (*it)->toString() << ") ";
    }

    ss << ") ( ";
    for (vector<shared_ptr<Term>>::iterator it = bodies.begin();
         it != bodies.end(); it++) {
        ss << "(" << (*it)->toString() << ") ";
    }

    ss << ") )";
    return ss.str();
}

/* ================================ DefineSortCommand ================================= */

DefineSortCommand::DefineSortCommand(shared_ptr<Symbol> symbol,
                                     const vector<shared_ptr<Symbol>> &params,
                                     shared_ptr<Sort> sort)
        : symbol(symbol), sort(sort) {
    this->params.insert(this->params.end(), params.begin(), params.end());
}

shared_ptr<Symbol> DefineSortCommand::getSymbol() const {
    return symbol;
}

void DefineSortCommand::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

vector<shared_ptr<Symbol>> &DefineSortCommand::getParams() {
    return params;
}

shared_ptr<Sort> DefineSortCommand::getSort() const {
    return sort;
}

void DefineSortCommand::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

void DefineSortCommand::accept(AstVisitor0* visitor) const {
    visitor->visit(this);
}

string DefineSortCommand::toString() {
    stringstream ss;
    ss << "( define-sort " << symbol->toString() << " ( ";
    for (vector<shared_ptr<Symbol>>::iterator it = params.begin();
         it != params.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ") " << sort->toString() << " )";
    return ss.str();
}

/* =================================== EchoCommand ==================================== */

string &EchoCommand::getMessage() {
    return message;
}

string EchoCommand::getMessage() const {
    return message;
}

void EchoCommand::setMessage(string message) {
    this->message = message;
}

void EchoCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string EchoCommand::toString() {
    stringstream ss;
    ss << "( echo " << message << " )";
    return ss.str();
}

/* =================================== ExitCommand ==================================== */

void ExitCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string ExitCommand::toString() {
    return "( exit )";
}

/* ================================ GetAssertsCommand ================================= */

void GetAssertsCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string GetAssertsCommand::toString() {
    return "( get-assertions )";
}

/* ================================ GetAssignsCommand ================================= */

void GetAssignsCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string GetAssignsCommand::toString() {
    return "( get-assignments )";
}

/* ================================== GetInfoCommand ================================== */

shared_ptr<Keyword> GetInfoCommand::getFlag() const {
    return flag;
}

void GetInfoCommand::setFlag(shared_ptr<Keyword> flag) {
    this->flag = flag;
}

void GetInfoCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string GetInfoCommand::toString() {
    stringstream ss;
    ss << "( get-info " << flag->toString() << " )";
    return ss.str();
}

/* ================================= GetModelCommand ================================== */

void GetModelCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string GetModelCommand::toString() {
    return "( get-model )";
}

/* ================================= GetOptionCommand ================================= */

shared_ptr<Keyword> GetOptionCommand::getOption() const {
    return option;
}

void GetOptionCommand::setOption(shared_ptr<Keyword> option) {
    this->option = option;
}

void GetOptionCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string GetOptionCommand::toString() {
    stringstream ss;
    ss << "( get-option " << option->toString() << " )";
    return ss.str();
}

/* ================================= GetProofCommand ================================== */

void GetProofCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string GetProofCommand::toString() {
    return "( get-proof )";
}

/* ============================== GetUnsatAssumsCommand =============================== */

void GetUnsatAssumsCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string GetUnsatAssumsCommand::toString() {
    return "( get-unsat-assumptions )";
}

/* =============================== GetUnsatCoreCommand ================================ */

void GetUnsatCoreCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string GetUnsatCoreCommand::toString() {
    return "( get-unsat-core )";
}

/* ================================= GetValueCommand ================================== */

GetValueCommand::GetValueCommand(const vector<shared_ptr<Term>> &terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

vector<shared_ptr<Term>> &GetValueCommand::getTerms() {
    return terms;
}

vector<shared_ptr<Term>> GetValueCommand::getTerms() const {
    return terms;
}

void GetValueCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string GetValueCommand::toString() {
    stringstream ss;
    ss << "( get-value ( ";

    for(vector<shared_ptr<Term>>::iterator it = terms.begin(); it != terms.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << ") )";
    return ss.str();
}

/* =================================== PopCommand ==================================== */

shared_ptr<NumeralLiteral> PopCommand::getNumeral() const {
    return numeral;
}

void PopCommand::setNumeral(shared_ptr<NumeralLiteral> numeral) {
    this->numeral = numeral;
}

void PopCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string PopCommand::toString() {
    stringstream ss;
    ss << "( pop " << numeral->toString() << " )";
    return ss.str();
}

/* =================================== PushCommand ==================================== */

shared_ptr<NumeralLiteral> PushCommand::getNumeral() const {
    return numeral;
}

void PushCommand::setNumeral(shared_ptr<NumeralLiteral> numeral) {
    this->numeral = numeral;
}

void PushCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string PushCommand::toString() {
    stringstream ss;
    ss << "( push " << numeral->toString() << " )";
    return ss.str();
}

/* =================================== ResetCommand =================================== */

void ResetCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string ResetCommand::toString() {
    return "( reset )";
}

/* =============================== ResetAssertsCommand ================================ */

void ResetAssertsCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string ResetAssertsCommand::toString() {
    return "( reset-assertions )";
}

/* ================================== SetInfoCommand ================================== */

shared_ptr<Attribute> SetInfoCommand::getInfo() const {
    return info;
}

void SetInfoCommand::setInfo(shared_ptr<Attribute> info) {
    this->info = info;
}

void SetInfoCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string SetInfoCommand::toString() {
    stringstream ss;
    ss << "( set-option " << info->getKeyword()->toString()
    << " " << info->getValue()->toString() << " )";
    return ss.str();
}

/* ================================= SetLogicCommand ================================== */

shared_ptr<Symbol> SetLogicCommand::getLogic() const {
    return logic;
}

void SetLogicCommand::setLogic(shared_ptr<Symbol> logic) {
    this->logic = logic;
}

void SetLogicCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string SetLogicCommand::toString() {
    stringstream ss;
    ss << "( set-logic " << logic->toString() << " )";
    return ss.str();
}

/* ================================= SetOptionCommand ================================= */

shared_ptr<Attribute> SetOptionCommand::getOption() const {
    return option;
}

void SetOptionCommand::setOption(shared_ptr<Attribute> option) {
    this->option = option;
}

void SetOptionCommand::accept(AstVisitor0* visitor) const {
     visitor->visit(this);
} 

string SetOptionCommand::toString() {
    stringstream ss;
    ss << "( set-option " << option->getKeyword()->toString()
    << " " << option->getValue()->toString() << " )";
    return ss.str();
}