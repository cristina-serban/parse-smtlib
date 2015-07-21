#ifndef PARSE_SMTLIB_SMT_EXECUTION_H
#define PARSE_SMTLIB_SMT_EXECUTION_H

#include "smt_execution_settings.h"
#include "parser/smt_parser.h"

#include <memory>

namespace smtlib {
    class SmtExecution {
    private:
        std::shared_ptr<SmtExecutionSettings> settings;
        std::shared_ptr<smtlib::ast::AstNode> ast;

        bool parseAttempted, parseSuccessful;
        bool syntaxCheckAttempted, syntaxCheckSuccessful;
        bool sortednessCheckAttempted, sortednessCheckSuccessful;

    public:
        SmtExecution();

        SmtExecution(std::shared_ptr<SmtExecutionSettings> settings);

        bool parse();

        bool checkSyntax();

        bool checkSortedness();
    };
}

#endif //PARSE_SMTLIB_SMT_ENGINE_H
