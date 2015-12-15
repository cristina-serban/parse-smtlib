#ifndef PARSE_SMTLIB_AST_VAR_REPLACER_H
#define PARSE_SMTLIB_AST_VAR_REPLACER_H

#include <unordered_map>
#include "ast_visitor_extra.h"
#include "../ast/ast_identifier.h"

namespace smtlib {
    namespace ast {

        class IVariableReplacerContext {
        public:
            virtual std::unordered_map<std::string, std::string>& getRenamingMap() = 0;
        };

        class VariableReplacerContext : public IVariableReplacerContext {
        private:
            std::unordered_map<std::string, std::string> renamingMap;
        public:
            virtual std::unordered_map<std::string, std::string>& getRenamingMap();
        };

        /* ================================= PredicateFinder ================================== */
        class VariableReplacer : public DummyVisitor0,
                                 public std::enable_shared_from_this<VariableReplacer> {
        private:
            std::shared_ptr<IVariableReplacerContext> ctx;

        public:
            inline VariableReplacer(std::shared_ptr<IVariableReplacerContext> ctx) : ctx(ctx) {}

            virtual void visit(std::shared_ptr<SimpleIdentifier> node);
            virtual void visit(std::shared_ptr<SortedVariable> node);
            virtual void visit(std::shared_ptr<VarBinding> node);
        };
    }
}

#endif //PARSE_SMTLIB_AST_VAR_REPLACER_H
