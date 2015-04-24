#include <sstream>
#include "smt_command.h"

using namespace std;
using namespace smt::ast;

/* ================================== AssertCommand =================================== */

AssertCommand::AssertCommand(shared_ptr<ITerm> term) {
    setTerm(term);
}

shared_ptr<ITerm> AssertCommand::getTerm() {
    return term;
}

void AssertCommand::setTerm(shared_ptr<ITerm> term) {
    this->term = term;
}

string AssertCommand::toString() {
    stringstream ss;
    ss << "( assert " << term->toString() << ")";
    return ss.str();
}

/* ================================= CheckSatCommand ================================== */

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

DeclareConstCommand::DeclareConstCommand(shared_ptr<Symbol> symbol,
                                         shared_ptr<Sort> sort) {
    setSymbol(symbol);
    setSort(sort);
}

shared_ptr<Symbol> DeclareConstCommand::getSymbol() {
    return symbol;
}

void DeclareConstCommand::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

shared_ptr<Sort> DeclareConstCommand::getSort() {
    return sort;
}

void DeclareConstCommand::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

string DeclareConstCommand::toString() {
    stringstream ss;
    ss << "( declare-const " << symbol->toString() << " " << sort->toString() << " )";
    return ss.str();
}

/* =============================== DeclareFunCommand ================================ */

DeclareFunCommand::DeclareFunCommand(shared_ptr<Symbol> symbol,
                                     const vector<shared_ptr<Sort>> &params,
                                     shared_ptr<Sort> sort) {
    setSymbol(symbol);
    this->params.insert(this->params.end(), params.begin(), params.end());
    setSort(sort);
}

shared_ptr<Symbol> DeclareFunCommand::getSymbol() {
    return symbol;
}

void DeclareFunCommand::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

vector<shared_ptr<Sort>> &DeclareFunCommand::getParams() {
    return params;
}

shared_ptr<Sort> DeclareFunCommand::getSort() {
    return sort;
}

void DeclareFunCommand::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

string DeclareFunCommand::toString() {
    stringstream ss;
    ss << "( declare-fun " << symbol << " ( ";

    for (vector<shared_ptr<Sort>>::iterator it = params.begin(); it != params.end(); it++) {
        ss << (*it)->toString() << " ";
    }

    ss << " ) " << sort->toString() << " )";

    return ss.str();
}

/* =============================== DeclareSortCommand ================================ */

DeclareSortCommand::DeclareSortCommand(shared_ptr<Symbol> symbol,
                                       shared_ptr<NumeralLiteral> arity) {
    setSymbol(symbol);
    setArity(arity);
}

shared_ptr<Symbol> DeclareSortCommand::getSymbol() {
    return symbol;
}

void DeclareSortCommand::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

shared_ptr<NumeralLiteral> DeclareSortCommand::getArity() {
    return arity;
}

void DeclareSortCommand::setArity(shared_ptr<NumeralLiteral> arity) {
    this->arity = arity;
}

string DeclareSortCommand::toString() {
    stringstream ss;
    ss << "( declare-sort " << symbol->toString() << " " << arity->toString() << " )";
    return ss.str();
}

/* ================================= DefineFunCommand ================================= */

DefineFunCommand::DefineFunCommand(shared_ptr<FunctionDefinition> definition) {
    setDefinition(definition);
}

DefineFunCommand::DefineFunCommand(shared_ptr<FunctionDeclaration> signature,
                                   shared_ptr<ITerm> body) {
    definition = make_shared<FunctionDefinition>(signature, body);
}

DefineFunCommand::DefineFunCommand(shared_ptr<Symbol> symbol,
                                   const vector<shared_ptr<SortedVariable>> &params,
                                   shared_ptr<Sort> sort,
                                   shared_ptr<ITerm> body) {
    definition = make_shared<FunctionDefinition>(symbol, params, sort, body);
}

shared_ptr<FunctionDefinition> DefineFunCommand::getDefinition() {
    return definition;
}

void DefineFunCommand::setDefinition(shared_ptr<FunctionDefinition> definition) {
    this->definition = definition;
}

/* ================================ DefineFunRecCommand =============================== */

DefineFunRecCommand::DefineFunRecCommand(shared_ptr<FunctionDefinition> definition) {
    setDefinition(definition);
}

DefineFunRecCommand::DefineFunRecCommand(shared_ptr<FunctionDeclaration> signature,
                                         shared_ptr<ITerm> body) {
    definition = make_shared<FunctionDefinition>(signature, body);
}

DefineFunRecCommand::DefineFunRecCommand(shared_ptr<Symbol> symbol,
                                         const vector<shared_ptr<SortedVariable>> &params,
                                         shared_ptr<Sort> sort,
                                         shared_ptr<ITerm> body) {
    definition = make_shared<FunctionDefinition>(symbol, params, sort, body);
}

shared_ptr<FunctionDefinition> DefineFunRecCommand::getDefinition() {
    return definition;
}

void DefineFunRecCommand::setDefinition(shared_ptr<FunctionDefinition> definition) {
    this->definition = definition;
}

/* =============================== DefineFunsRecCommand =============================== */

DefineFunsRecCommand::DefineFunsRecCommand(
        const vector<shared_ptr<FunctionDefinition>> &definitions) {
    this->definitions.insert(this->definitions.end(), definitions.begin(), definitions.end());
}

vector<shared_ptr<FunctionDefinition>> &DefineFunsRecCommand::getDefinitions() {
    return definitions;
}

/* ================================ DefineSortCommand ================================= */

DefineSortCommand::DefineSortCommand(shared_ptr<Symbol> symbol,
                                     const vector<shared_ptr<Symbol>> &params,
                                     shared_ptr<Sort> sort) {
    setSymbol(symbol);
    this->params.insert(this->params.end(), params.begin(), params.end());
    setSort(sort);
}

shared_ptr<Symbol> DefineSortCommand::getSymbol() {
    return symbol;
}

void DefineSortCommand::setSymbol(shared_ptr<Symbol> symbol) {
    this->symbol = symbol;
}

vector<shared_ptr<Symbol>> &DefineSortCommand::getParams() {
    return params;
}

shared_ptr<Sort> DefineSortCommand::getSort() {
    return sort;
}

void DefineSortCommand::setSort(shared_ptr<Sort> sort) {
    this->sort = sort;
}

/* =================================== ExitCommand ==================================== */

string ExitCommand::toString() {
    return "( exit )";
}

/* ================================ GetAssertsCommand ================================= */

string GetAssertsCommand::toString() {
    return "( get-assertions )";
}

/* ================================ GetAssignsCommand ================================= */

string GetAssignsCommand::toString() {
    return "( get-assignments )";
}

/* ================================== GetInfoCommand ================================== */
GetInfoCommand::GetInfoCommand(shared_ptr<Keyword> flag) {
    setFlag(flag);
}

shared_ptr<Keyword> GetInfoCommand::getFlag() {
    return flag;
}

void GetInfoCommand::setFlag(shared_ptr<Keyword> flag) {
    this->flag = flag;
}

/* ================================= GetModelCommand ================================== */

string GetModelCommand::toString() {
    return "( get-model )";
}

/* ================================= GetOptionCommand ================================= */

GetOptionCommand::GetOptionCommand(shared_ptr<Keyword> option) {
    setOption(option);
}

shared_ptr<Keyword> GetOptionCommand::getOption() {
    return option;
}

void GetOptionCommand::setOption(shared_ptr<Keyword> option) {
    this->option = option;
}

/* ================================= GetProofCommand ================================== */

string GetProofCommand::toString() {
    return "( get-proof )";
}

/* =============================== GetUnsatCoreCommand ================================ */

string GetUnsatCoreCommand::toString() {
    return "( get-unsat-core )";
}

/* ================================= GetValueCommand ================================== */

GetValueCommand::GetValueCommand(const vector<shared_ptr<ITerm>> &terms) {
    this->terms.insert(this->terms.end(), terms.begin(), terms.end());
}

vector<shared_ptr<ITerm>> &GetValueCommand::getTerms() {
    return terms;
}

/* =================================== PopCommand ==================================== */

PopCommand::PopCommand(shared_ptr<NumeralLiteral> numeral) {
    setNumeral(numeral);
}

shared_ptr<NumeralLiteral> PopCommand::getNumeral() {
    return numeral;
}

void PopCommand::setNumeral(shared_ptr<NumeralLiteral> numeral) {
    this->numeral = numeral;
}

string PopCommand::toString() {
    stringstream ss;
    ss << "( push " << numeral->toString() << " )";
    return ss.str();
}

/* =================================== PushCommand ==================================== */

PushCommand::PushCommand(shared_ptr<NumeralLiteral> numeral) {
    setNumeral(numeral);
}

shared_ptr<NumeralLiteral> PushCommand::getNumeral() {
    return numeral;
}

void PushCommand::setNumeral(shared_ptr<NumeralLiteral> numeral) {
    this->numeral = numeral;
}

string PushCommand::toString() {
    stringstream ss;
    ss << "( push " << numeral->toString() << " )";
    return ss.str();
}

/* =================================== ResetCommand =================================== */

string ResetCommand::toString() {
    return "( reset )";
}

/* =============================== ResetAssertsCommand ================================ */

string ResetAssertsCommand::toString() {
    return "( reset-assertions )";
}

/* ================================== SetInfoCommand ================================== */

SetInfoCommand::SetInfoCommand(shared_ptr<Attribute> info) {
    setInfo(info);
}

shared_ptr<Attribute> SetInfoCommand::getInfo() {
    return info;
}

void SetInfoCommand::setInfo(shared_ptr<Attribute> info) {
    this->info = info;
}

string SetInfoCommand::toString() {
    stringstream ss;
    ss << "( set-option " << info->getKeyword()->toString()
    << " " << info->getValue()->toString() << " )";
    return ss.str();
}

/* ================================= SetLogicCommand ================================== */

SetLogicCommand::SetLogicCommand(shared_ptr<Symbol> logic) {
    setLogic(logic);
}

shared_ptr<Symbol> SetLogicCommand::getLogic() {
    return logic;
}

void SetLogicCommand::setLogic(shared_ptr<Symbol> logic) {
    this->logic = logic;
}

string SetLogicCommand::toString() {
    stringstream ss;
    ss << "( set-logic " << logic->toString() << " )";
    return ss.str();
}

/* ================================= SetOptionCommand ================================= */

SetOptionCommand::SetOptionCommand(shared_ptr<Attribute> option) {
    setOption(option);
}

shared_ptr<Attribute> SetOptionCommand::getOption() {
    return option;
}

void SetOptionCommand::setOption(shared_ptr<Attribute> option) {
    this->option = option;
}

string SetOptionCommand::toString() {
    stringstream ss;
    ss << "( set-option " << option->getKeyword()->toString()
    << " " << option->getValue()->toString() << " )";
    return ss.str();
}