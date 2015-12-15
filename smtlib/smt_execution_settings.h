#ifndef PARSE_SMTLIB_SMT_EXECUTION_SETTINGS_H
#define PARSE_SMTLIB_SMT_EXECUTION_SETTINGS_H

#include "ast/ast_abstract.h"
#include "parser/smt_symbol_stack.h"
#include "visitor/ast_sortedness_checker.h"

#include <memory>

namespace smtlib {
    class SmtExecutionSettings {
    public:
        enum InputMethod { INPUT_NONE = 0, INPUT_FILE, INPUT_AST };
    private:
        bool coreTheoryEnabled;
        std::string filename;
        std::shared_ptr<smtlib::ast::AstNode> ast;
        std::shared_ptr<smtlib::ast::ISortCheckContext> sortCheckContext;
        InputMethod inputMethod;
        bool unfoldExistential = true;
        int unfoldLevel = 0;
        std::string unfoldOutputPath = "unfolding";
    public:
        SmtExecutionSettings();

        SmtExecutionSettings(std::shared_ptr<SmtExecutionSettings> settings);

        inline bool isCoreTheoryEnabled() { return coreTheoryEnabled; }

        inline void setCoreTheoryEnabled(bool enabled) { coreTheoryEnabled = enabled; }

        void setInputFromFile(std::string filename);

        void setInputFromAst(std::shared_ptr<smtlib::ast::AstNode> ast);

        inline void setSortCheckContext(std::shared_ptr<smtlib::ast::ISortCheckContext> ctx) {
            this->sortCheckContext = ctx;
        }

        inline std::string getFilename() { return filename; }

        inline std::shared_ptr<smtlib::ast::AstNode> getAst() { return ast; }

        inline std::shared_ptr<smtlib::ast::ISortCheckContext> getSortCheckContext()
        {
            return sortCheckContext;
        }

        inline InputMethod getInputMethod() { return inputMethod; }

        inline bool isUnfoldExistential() { return unfoldExistential; }

        inline void setUnfoldExistential(bool unfoldExistential) { this->unfoldExistential = unfoldExistential; };

        inline int getUnfoldLevel() { return unfoldLevel; }

        inline void setUnfoldLevel(int unfoldLevel) { this->unfoldLevel = unfoldLevel; }

        inline std::string getUnfoldOutputPath() { return unfoldOutputPath; }

        inline void setUnfoldOutputPath(std::string unfoldOutputPath) {
            this->unfoldOutputPath = unfoldOutputPath;
        }
    };
}

#endif //PARSE_SMTLIB_SMT_ENGINE_SETTINGS_H
