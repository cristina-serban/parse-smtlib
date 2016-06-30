#ifndef PARSE_SMTLIB_AST_TERM_SORTER_H
#define PARSE_SMTLIB_AST_TERM_SORTER_H

#include "ast_visitor_extra.h"
#include "../parser/smt_symbol_stack.h"
#include "../util/configuration.h"

#include <algorithm>

namespace smtlib {
    namespace ast {
        class SortednessChecker;

        class ITermSorterContext {
        public:
            virtual std::shared_ptr<SymbolStack> getStack() = 0;
            virtual std::shared_ptr<SortednessChecker> getChecker() = 0;
            virtual std::shared_ptr<Configuration> getConfiguration() = 0;
        };

        class TermSorter : public DummyAstVisitor1<std::shared_ptr<Sort>> {
        private:
            std::shared_ptr<ITermSorterContext> ctx;

            bool getParamMapping(std::vector<std::string> &params,
                                 std::unordered_map<std::string, std::shared_ptr<Sort>> &mapping,
                                 std::shared_ptr<Sort> sort1,
                                 std::shared_ptr<Sort> sort2);

        public:
            inline TermSorter(std::shared_ptr<ITermSorterContext> ctx) : ctx(ctx) { }

            virtual void visit(std::shared_ptr<SimpleIdentifier> node);

            virtual void visit(std::shared_ptr<QualifiedIdentifier> node);

            virtual void visit(std::shared_ptr<DecimalLiteral> node);

            virtual void visit(std::shared_ptr<NumeralLiteral> node);

            virtual void visit(std::shared_ptr<StringLiteral> node);

            virtual void visit(std::shared_ptr<QualifiedTerm> node);

            virtual void visit(std::shared_ptr<LetTerm> node);

            virtual void visit(std::shared_ptr<ForallTerm> node);

            virtual void visit(std::shared_ptr<ExistsTerm> node);

            virtual void visit(std::shared_ptr<MatchTerm> node);

            virtual void visit(std::shared_ptr<AnnotatedTerm> node);

            std::shared_ptr<Sort> run(std::shared_ptr<AstNode> node) {
                return wrappedVisit(node);
            }
        };
    }
}


#endif //PARSE_SMTLIB_AST_TERM_SORTER_H
