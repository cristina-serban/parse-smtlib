#ifndef PARSE_SMTLIB_AST_SORTEDNESS_CHECKER_H
#define PARSE_SMTLIB_AST_SORTEDNESS_CHECKER_H

#include "ast_visitor_extra.h"
#include "ast_syntax_checker.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_command.h"
#include "../parser/smt_symbol_stack.h"
#include "../util/smt_logger.h"

#include <map>

namespace smtlib {
    namespace ast {
        class SortednessChecker : public DummyAstVisitor2<bool, std::shared_ptr<SymbolStack>> {
        private:
            struct SortednessCheckErrorInfo {
                std::string message;
                std::shared_ptr<SortInfo> sortInfo;
                std::shared_ptr<FunInfo> funInfo;
            };

            struct SortednessCheckError {
                std::vector<std::shared_ptr<SortednessCheckErrorInfo>> infos;
                std::shared_ptr<AstNode> node;
            };

            struct TermSorterInfo {
                std::shared_ptr<SymbolStack> stack;
                SortednessChecker* checker;
                std::shared_ptr<AstNode> source;

                TermSorterInfo(std::shared_ptr<SymbolStack> stack,
                               SortednessChecker* checker,
                               std::shared_ptr<AstNode> source) {
                    this->stack = stack;
                    this->checker = checker;
                    this->source = source;
                }
            };

            std::map<std::string, std::vector<std::shared_ptr<SortednessCheckError>>> errors;

            std::shared_ptr<SortednessCheckError> addError(std::string message, std::shared_ptr<AstNode> node,
                                                           std::shared_ptr<SortednessCheckError> err);
            std::shared_ptr<SortednessCheckError> addError(std::string message, std::shared_ptr<AstNode> node,
                                                           std::shared_ptr<SortInfo> sortInfo,
                                                           std::shared_ptr<SortednessCheckError> err);
            std::shared_ptr<SortednessCheckError> addError(std::string message, std::shared_ptr<AstNode> node,
                                                           std::shared_ptr<FunInfo> funInfo,
                                                           std::shared_ptr<SortednessCheckError> err);

            void addError(std::string message, std::shared_ptr<AstNode> node);
            void addError(std::string message, std::shared_ptr<AstNode> node, std::shared_ptr<SortInfo> sortInfo);
            void addError(std::string message, std::shared_ptr<AstNode> node, std::shared_ptr<FunInfo> funInfo);

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

            void loadTheory(std::string theory);
            void loadLogic(std::string logic);

            std::shared_ptr<SortednessCheckError> checkSort(std::shared_ptr<Sort> sort,
                                                            std::shared_ptr<AstNode> source,
                                                            std::shared_ptr<SortednessCheckError> err);

            std::shared_ptr<SortednessCheckError> checkSort(std::vector<std::shared_ptr<Symbol>> params,
                                                            std::unordered_map<std::string, bool>& paramUsage,
                                                            std::shared_ptr<Sort> sort,
                                                            std::shared_ptr<AstNode> source,
                                                            std::shared_ptr<SortednessCheckError> err);

            class TermSorter : public DummyAstVisitor2<std::shared_ptr<Sort>, std::shared_ptr<TermSorterInfo>> {

            public:
                virtual void visit(std::shared_ptr<SimpleIdentifier> node);
                virtual void visit(std::shared_ptr<QualifiedIdentifier> node);

                virtual void visit(std::shared_ptr<DecimalLiteral> node);
                virtual void visit(std::shared_ptr<NumeralLiteral> node);
                virtual void visit(std::shared_ptr<StringLiteral> node);

                virtual void visit(std::shared_ptr<QualifiedTerm> node);
                virtual void visit(std::shared_ptr<LetTerm> node);
                virtual void visit(std::shared_ptr<ForallTerm> node);
                virtual void visit(std::shared_ptr<ExistsTerm> node);
                virtual void visit(std::shared_ptr<AnnotatedTerm> node);
            };

        public:
            virtual void visit(std::shared_ptr<AssertCommand> node);
            virtual void visit(std::shared_ptr<DeclareConstCommand> node);
            virtual void visit(std::shared_ptr<DeclareFunCommand> node);
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

            virtual bool run (std::shared_ptr<SymbolStack> stack, std::shared_ptr<AstNode> node) {
                if(node) {
                    SyntaxChecker* chk = new SyntaxChecker();
                    if(chk->run(node)) {
                        ret = true;
                        arg = stack;
                        loadTheory("Core");
                        return wrappedVisit(stack, node);
                    } else {
                        Logger::syntaxError("SortednessChecker::run()", node->getFilename()->c_str(), chk->getErrors().c_str());
                        std::string msg = "File '" + std::string(node->getFilename()->c_str()) +
                                          "' contains syntax errors. Cannot check well-sortedness";
                        Logger::error("SortednessChecker::run()", msg.c_str());
                        return false;
                    }
                } else {
                    Logger::warning("SortednessChecker::run()", "Attempting to check an empty abstract syntax tree");
                    return false;
                }
            }

            std::string getErrors();
        };
    }
}

#endif //PARSE_SMTLIB_AST_SORTEDNESS_CHECKER_H
