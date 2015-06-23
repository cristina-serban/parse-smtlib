#ifndef PARSE_SMTLIB_AST_SORTEDNESS_CHECKER_H
#define PARSE_SMTLIB_AST_SORTEDNESS_CHECKER_H

#include "ast_visitor_extra.h"
#include "../parser/smt_symbol_stack.h"

namespace smtlib {
    namespace ast {
        class SortednessChecker : public DummyAstVisitor2<bool, std::shared_ptr<SymbolStack>> {
        private:
            struct SortednessCheckError {
                std::vector<std::string> messages;
                AstNode const *node;
                std::shared_ptr<SortInfo> sortInfo;
                std::shared_ptr<FunInfo> funInfo;
            };

            std::unordered_map<std::string, std::vector<std::shared_ptr<SortednessCheckError>>> errors;

            std::shared_ptr<SortednessCheckError> addError(std::string message, AstNode const *node,
                                                           std::shared_ptr<SortednessCheckError> err);
            std::shared_ptr<SortednessCheckError> addError(std::string message, AstNode const *node,
                                                           std::shared_ptr<SortInfo> sortInfo,
                                                           std::shared_ptr<SortednessCheckError> err);
            std::shared_ptr<SortednessCheckError> addError(std::string message, AstNode const *node,
                                                           std::shared_ptr<FunInfo> funInfo,
                                                           std::shared_ptr<SortednessCheckError> err);

            void addError(std::string message, AstNode const *node);
            void addError(std::string message, AstNode const *node, std::shared_ptr<SortInfo> sortInfo);
            void addError(std::string message, AstNode const *node, std::shared_ptr<FunInfo> funInfo);

            bool equalSignatures(const std::vector<std::shared_ptr<ast::Sort>> &sig1,
                                 const std::vector<std::shared_ptr<ast::Sort>> &sig2);

            bool equalParamSignatures(const std::vector<std::shared_ptr<ast::Symbol>> &params1,
                                      const std::vector<std::shared_ptr<ast::Sort>> &sig1,
                                      const std::vector<std::shared_ptr<ast::Symbol>> &params,
                                      const std::vector<std::shared_ptr<ast::Sort>> &sig2);

            bool equalParamSorts(const std::vector<std::shared_ptr<ast::Symbol>> &params1,
                                 const std::shared_ptr<ast::Sort> sort1,
                                 const std::vector<std::shared_ptr<ast::Symbol>> &params2,
                                 const std::shared_ptr<ast::Sort> sort2,
                                 std::unordered_map<std::string, std::string> &mapping);

            std::shared_ptr<SortInfo> duplicate(SortSymbolDeclaration const *node);
            std::shared_ptr<FunInfo> duplicate(SpecConstFunDeclaration const *node);
            std::shared_ptr<FunInfo> duplicate(MetaSpecConstFunDeclaration const *node);
            std::shared_ptr<FunInfo> duplicate(IdentifierFunDeclaration const *node);
            std::shared_ptr<FunInfo> duplicate(ParametricFunDeclaration const *node);

        public:
            virtual void visit(AssertCommand const *node);
            virtual void visit(DeclareConstCommand const *node);
            virtual void visit(DeclareFunCommand const *node);
            virtual void visit(DeclareSortCommand const *node);
            virtual void visit(DefineFunCommand const *node);
            virtual void visit(DefineFunRecCommand const *node);
            virtual void visit(DefineFunsRecCommand const *node);
            virtual void visit(DefineSortCommand const *node);
            virtual void visit(GetValueCommand const *node);
            virtual void visit(PopCommand const *node);
            virtual void visit(PushCommand const *node);
            virtual void visit(ResetCommand const *node);

            virtual void visit(FunctionDeclaration const *node);
            virtual void visit(FunctionDefinition const *node);

            virtual void visit(Identifier const *node);
            virtual void visit(QualifiedIdentifier const *node);

            virtual void visit(DecimalLiteral const *node);
            virtual void visit(NumeralLiteral const *node);
            virtual void visit(StringLiteral const *node);

            virtual void visit(Logic const *node);
            virtual void visit(Theory const *node);
            virtual void visit(Script const *node);

            virtual void visit(Sort const *node);

            virtual void visit(CompSExpression const *node);

            virtual void visit(SortSymbolDeclaration const *node);

            virtual void visit(SpecConstFunDeclaration const *node);
            virtual void visit(MetaSpecConstFunDeclaration const *node);
            virtual void visit(IdentifierFunDeclaration const *node);
            virtual void visit(ParametricFunDeclaration const *node);

            virtual void visit(QualifiedTerm const *node);
            virtual void visit(LetTerm const *node);
            virtual void visit(ForallTerm const *node);
            virtual void visit(ExistsTerm const *node);
            virtual void visit(AnnotatedTerm const *node);

            virtual void visit(SortedVariable const *node);
            virtual void visit(VarBinding const *node);

            virtual bool run (std::shared_ptr<SymbolStack> stack, AstNode const *node) {
                ret = true;
                return wrappedVisit(stack, node);
            }
        };
    }
}

#endif //PARSE_SMTLIB_AST_SORTEDNESS_CHECKER_H
