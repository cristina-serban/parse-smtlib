#include "smt_execution_settings.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

SmtExecutionSettings::SmtExecutionSettings()
        : coreTheoryEnabled(true), inputMethod(INPUT_NONE) {}

SmtExecutionSettings::SmtExecutionSettings(shared_ptr<SmtExecutionSettings> settings) {
    this->coreTheoryEnabled = settings->coreTheoryEnabled;
    this->inputMethod = settings->inputMethod;
    this->filename = settings->filename;
    this->ast = settings->ast;
    this->stack = settings->stack;
}

void SmtExecutionSettings::setInputFromFile(std::string filename) {
    this->filename = filename;
    this->ast.reset();
    inputMethod = INPUT_FILE;
}

void SmtExecutionSettings::setInputFromAst(std::shared_ptr<smtlib::ast::AstNode> ast) {
    this->ast = ast;
    this->filename = "";
    inputMethod = INPUT_AST;
}