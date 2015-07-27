#ifndef PARSE_SMTLIB_SMT_EXECUTION_SETTINGS_H
#define PARSE_SMTLIB_SMT_EXECUTION_SETTINGS_H

#include "ast/ast_abstract.h"
#include "parser/smt_symbol_stack.h"

#include <memory>

namespace smtlib {
    class SmtExecutionSettings {
    public:
        enum InputMethod { INPUT_NONE = 0, INPUT_FILE, INPUT_AST };
    private:
        bool coreTheoryEnabled;
        std::string filename;
        std::shared_ptr<smtlib::ast::AstNode> ast;
        std::shared_ptr<smtlib::SymbolStack> stack;
        InputMethod inputMethod;
    public:
        SmtExecutionSettings();

        SmtExecutionSettings(std::shared_ptr<SmtExecutionSettings> settings);

        inline bool isCoreTheoryEnabled() { return coreTheoryEnabled; }

        inline void setCoreTheoryEnabled(bool enabled) { coreTheoryEnabled = enabled; }

        void setInputFromFile(std::string filename);

        void setInputFromAst(std::shared_ptr<smtlib::ast::AstNode> ast);

        void setStack(std::shared_ptr<smtlib::SymbolStack> stack) { this->stack = stack; }

        inline std::string getFilename() { return filename; }

        inline std::shared_ptr<smtlib::ast::AstNode> getAst() { return ast; }

        inline std::shared_ptr<smtlib::SymbolStack> getStack() { return stack; }

        inline InputMethod getInputMethod() { return inputMethod; }
    };

}

#endif //PARSE_SMTLIB_SMT_ENGINE_SETTINGS_H
