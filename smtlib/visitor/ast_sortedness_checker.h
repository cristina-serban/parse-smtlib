#ifndef PARSE_SMTLIB_AST_SORTEDNESS_CHECKER_H
#define PARSE_SMTLIB_AST_SORTEDNESS_CHECKER_H

#include "ast_visitor_extra.h"
#include "ast_term_sorter.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_command.h"
#include "../parser/smt_symbol_stack.h"
#include "../util/logger.h"

#include <map>

namespace smtlib {
    namespace ast {
        class ISortCheckContext {
        public:
            virtual std::shared_ptr<SymbolStack> getStack() = 0;
            virtual std::vector<std::string>& getCurrentTheories() = 0;
            virtual std::string getCurrentLogic() = 0;
            virtual void setCurrentLogic(std::string logic) = 0;
        };

        class SortednessCheckerContext : public ISortCheckContext,
                                         public std::enable_shared_from_this<SortednessCheckerContext> {
        private:
            std::shared_ptr<smtlib::SymbolStack> stack;
            std::vector<std::string> currentTheories;
            std::string currentLogic;
        public:
            SortednessCheckerContext();

            SortednessCheckerContext(std::shared_ptr<smtlib::SymbolStack> stack);

            virtual std::shared_ptr<SymbolStack> getStack();
            virtual std::vector<std::string>& getCurrentTheories();
            virtual std::string getCurrentLogic();
            virtual void setCurrentLogic(std::string logic);
        };

        class SortednessChecker : public DummyVisitor0,
                                  public ITermSorterContext,
                                  public std::enable_shared_from_this<SortednessChecker>{
        public:
            struct Error {
                std::string message;
                std::shared_ptr<SymbolInfo> info;

                Error(std::string message) : message(message) { }

                Error(std::string message, std::shared_ptr<SymbolInfo> info)
                        : message(message), info(info) { }
            };

            struct NodeError {
                std::vector<std::shared_ptr<Error>> errs;
                std::shared_ptr<AstNode> node;

                NodeError() { }

                NodeError(std::shared_ptr<Error> err, std::shared_ptr<AstNode> node) {
                    errs.push_back(err);
                    this->node = node;
                }

                NodeError(std::vector<std::shared_ptr<Error>> &errs,
                          std::shared_ptr<AstNode> node) {
                    this->errs.insert(this->errs.begin(), errs.begin(), errs.end());
                    this->node = node;
                }
            };
        private:
            std::shared_ptr<ISortCheckContext> ctx;
            std::map<std::string, std::vector<std::shared_ptr<NodeError>>> errors;

            std::shared_ptr<SortInfo> getInfo(std::shared_ptr<SortSymbolDeclaration> node);

            std::shared_ptr<SortInfo> getInfo(std::shared_ptr<DeclareSortCommand> node);

            std::shared_ptr<SortInfo> getInfo(std::shared_ptr<DefineSortCommand> node);

            std::shared_ptr<FunInfo> getInfo(std::shared_ptr<SpecConstFunDeclaration> node);

            std::shared_ptr<FunInfo> getInfo(std::shared_ptr<MetaSpecConstFunDeclaration> nodetd);

            std::shared_ptr<FunInfo> getInfo(std::shared_ptr<SimpleFunDeclaration> node);

            std::shared_ptr<FunInfo> getInfo(std::shared_ptr<ParametricFunDeclaration> node);

            std::shared_ptr<FunInfo> getInfo(std::shared_ptr<DeclareConstCommand> node);

            std::shared_ptr<FunInfo> getInfo(std::shared_ptr<DeclareFunCommand> node);

            std::shared_ptr<FunInfo> getInfo(std::shared_ptr<DefineFunCommand> node);

            std::shared_ptr<FunInfo> getInfo(std::shared_ptr<DefineFunRecCommand> node);

            std::vector<std::shared_ptr<FunInfo>> getInfo(std::shared_ptr<DefineFunsRecCommand> node);

            std::vector<std::shared_ptr<SymbolInfo>> getInfo(std::shared_ptr<DeclareDatatypeCommand> node);

            std::vector<std::shared_ptr<SymbolInfo>> getInfo(std::shared_ptr<DeclareDatatypesCommand> node);

            void loadTheory(std::string theory,
                            std::shared_ptr<AstNode> node,
                            std::shared_ptr<NodeError> err);

            void loadLogic(std::string logic,
                           std::shared_ptr<AstNode> node,
                           std::shared_ptr<NodeError> err);

        public:
            inline SortednessChecker() : ctx(std::make_shared<SortednessCheckerContext>()) { }

            inline SortednessChecker(std::shared_ptr<ISortCheckContext> ctx) : ctx(ctx) { }

            std::shared_ptr<NodeError> addError(std::string message,
                                                std::shared_ptr<AstNode> node,
                                                std::shared_ptr<NodeError> err);

            std::shared_ptr<NodeError> addError(std::string message,
                                                std::shared_ptr<AstNode> node,
                                                std::shared_ptr<SymbolInfo> symbolInfo,
                                                std::shared_ptr<NodeError> err);

            void addError(std::string message,
                          std::shared_ptr<AstNode> node);

            void addError(std::string message,
                          std::shared_ptr<AstNode> node,
                          std::shared_ptr<SymbolInfo> err);

            void loadTheory(std::string theory);

            std::shared_ptr<NodeError> checkSort(std::shared_ptr<Sort> sort,
                                                 std::shared_ptr<AstNode> source,
                                                 std::shared_ptr<NodeError> err);

            std::shared_ptr<NodeError> checkSort(std::vector<std::shared_ptr<Symbol>> &params,
                                                 std::shared_ptr<Sort> sort,
                                                 std::shared_ptr<AstNode> source,
                                                 std::shared_ptr<NodeError> err);

            virtual void visit(std::shared_ptr<AssertCommand> node);

            virtual void visit(std::shared_ptr<DeclareConstCommand> node);

            virtual void visit(std::shared_ptr<DeclareFunCommand> node);

            virtual void visit(std::shared_ptr<DeclareDatatypeCommand> node);

            virtual void visit(std::shared_ptr<DeclareDatatypesCommand> node);

            virtual void visit(std::shared_ptr<DeclareSortCommand> node);

            virtual void visit(std::shared_ptr<DefineFunCommand> node);

            virtual void visit(std::shared_ptr<DefineFunRecCommand> node);

            virtual void visit(std::shared_ptr<DefineFunsRecCommand> node);

            virtual void visit(std::shared_ptr<DefineSortCommand> node);

            virtual void visit(std::shared_ptr<GetValueCommand> node);

            virtual void visit(std::shared_ptr<PopCommand> node);

            virtual void visit(std::shared_ptr<PushCommand> node);

            virtual void visit(std::shared_ptr<ResetCommand> node);

            virtual void visit(std::shared_ptr<SetLogicCommand> node);

            virtual void visit(std::shared_ptr<Logic> node);

            virtual void visit(std::shared_ptr<Theory> node);

            virtual void visit(std::shared_ptr<Script> node);

            virtual void visit(std::shared_ptr<SortSymbolDeclaration> node);

            virtual void visit(std::shared_ptr<SpecConstFunDeclaration> node);

            virtual void visit(std::shared_ptr<MetaSpecConstFunDeclaration> node);

            virtual void visit(std::shared_ptr<SimpleFunDeclaration> node);

            virtual void visit(std::shared_ptr<ParametricFunDeclaration> node);

            bool check(std::shared_ptr<AstNode> node);

            std::string getErrors();

            // ITermSorterContext implementation
            virtual std::shared_ptr<SymbolStack> getStack();

            virtual std::shared_ptr<SortednessChecker> getChecker();
        };
    }
}

#endif //PARSE_SMTLIB_AST_SORTEDNESS_CHECKER_H
