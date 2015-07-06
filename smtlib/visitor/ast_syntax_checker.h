#ifndef PARSE_SMTLIB_AST_SYNTAX_CHECKER_H
#define PARSE_SMTLIB_AST_SYNTAX_CHECKER_H

#include "ast_visitor_extra.h"

#include <regex>
#include <string>
#include <vector>

namespace smtlib {
    namespace ast {
        class SyntaxChecker : public DummyAstVisitor1<bool> {
        private:
            struct SyntaxCheckError {
                std::vector<std::string> messages;
                std::shared_ptr<AstNode> node;

                SyntaxCheckError() { }

                SyntaxCheckError(std::vector<std::string>& messages,
                                 std::shared_ptr<AstNode> node) : node(node) {
                    this->messages.insert(this->messages.begin(), messages.begin(), messages.end());
                }
            };

            std::vector<std::shared_ptr<SyntaxCheckError>> errors;

            const std::regex regexSymbol = std::regex(
                    "^([a-zA-Z+\\-/*=%?!.$_~&^<>@][a-zA-Z0-9+\\-/*=%?!.$_~&^<>@]*)|(\\|[\\x20-\\x5B\\x5D-\\x7B\\x7D\\x7E\\xA0-\\xFF\\x09\\r\\n \\xA0]*\\|)$");
            const std::regex regexKeyword = std::regex(
                    "^:([a-zA-Z+\\-/*=%?!.$_~&^<>@][a-zA-Z0-9+\\-/*=%?!.$_~&^<>@]*)|(\\|[\\x20-\\x5B\\x5D-\\x7B\\x7D\\x7E\\xA0-\\xFF\\x09\\r\\n \\xA0]*\\|)$");

            std::shared_ptr<SyntaxCheckError> addError(std::string message, std::shared_ptr<AstNode> node,
                                                       std::shared_ptr<SyntaxCheckError> err);
        public:
            virtual void visit(std::shared_ptr<Attribute> node);
            virtual void visit(std::shared_ptr<CompAttributeValue> node);

            virtual void visit(std::shared_ptr<Symbol> node);
            virtual void visit(std::shared_ptr<Keyword> node);
            virtual void visit(std::shared_ptr<MetaSpecConstant> node);
            virtual void visit(std::shared_ptr<BooleanValue> node);
            virtual void visit(std::shared_ptr<PropLiteral> node);

            virtual void visit(std::shared_ptr<AssertCommand> node);
            virtual void visit(std::shared_ptr<CheckSatCommand> node);
            virtual void visit(std::shared_ptr<CheckSatAssumCommand> node);
            virtual void visit(std::shared_ptr<DeclareConstCommand> node);
            virtual void visit(std::shared_ptr<DeclareDatatypeCommand> node);
            virtual void visit(std::shared_ptr<DeclareDatatypesCommand> node);
            virtual void visit(std::shared_ptr<DeclareFunCommand> node);
            virtual void visit(std::shared_ptr<DeclareSortCommand> node);
            virtual void visit(std::shared_ptr<DefineFunCommand> node);
            virtual void visit(std::shared_ptr<DefineFunRecCommand> node);
            virtual void visit(std::shared_ptr<DefineFunsRecCommand> node);
            virtual void visit(std::shared_ptr<DefineSortCommand> node);
            virtual void visit(std::shared_ptr<EchoCommand> node);
            virtual void visit(std::shared_ptr<ExitCommand> node);
            virtual void visit(std::shared_ptr<GetAssertsCommand> node);
            virtual void visit(std::shared_ptr<GetAssignsCommand> node);
            virtual void visit(std::shared_ptr<GetInfoCommand> node);
            virtual void visit(std::shared_ptr<GetModelCommand> node);
            virtual void visit(std::shared_ptr<GetOptionCommand> node);
            virtual void visit(std::shared_ptr<GetProofCommand> node);
            virtual void visit(std::shared_ptr<GetUnsatAssumsCommand> node);
            virtual void visit(std::shared_ptr<GetUnsatCoreCommand> node);
            virtual void visit(std::shared_ptr<GetValueCommand> node);
            virtual void visit(std::shared_ptr<PopCommand> node);
            virtual void visit(std::shared_ptr<PushCommand> node);
            virtual void visit(std::shared_ptr<ResetCommand> node);
            virtual void visit(std::shared_ptr<ResetAssertsCommand> node);
            virtual void visit(std::shared_ptr<SetInfoCommand> node);
            virtual void visit(std::shared_ptr<SetLogicCommand> node);
            virtual void visit(std::shared_ptr<SetOptionCommand> node);

            virtual void visit(std::shared_ptr<FunctionDeclaration> node);
            virtual void visit(std::shared_ptr<FunctionDefinition> node);

            virtual void visit(std::shared_ptr<SimpleIdentifier> node);
            virtual void visit(std::shared_ptr<QualifiedIdentifier> node);

            virtual void visit(std::shared_ptr<DecimalLiteral> node);
            virtual void visit(std::shared_ptr<NumeralLiteral> node);
            virtual void visit(std::shared_ptr<StringLiteral> node);

            virtual void visit(std::shared_ptr<Logic> node);
            virtual void visit(std::shared_ptr<Theory> node);
            virtual void visit(std::shared_ptr<Script> node);

            virtual void visit(std::shared_ptr<Sort> node);

            virtual void visit(std::shared_ptr<CompSExpression> node);

            virtual void visit(std::shared_ptr<SortSymbolDeclaration> node);

            virtual void visit(std::shared_ptr<SpecConstFunDeclaration> node);
            virtual void visit(std::shared_ptr<MetaSpecConstFunDeclaration> node);
            virtual void visit(std::shared_ptr<SimpleFunDeclaration> node);
            virtual void visit(std::shared_ptr<ParametricFunDeclaration> node);

            virtual void visit(std::shared_ptr<SortDeclaration> node);
            virtual void visit(std::shared_ptr<SelectorDeclaration> node);
            virtual void visit(std::shared_ptr<ConstructorDeclaration> node);
            virtual void visit(std::shared_ptr<SimpleDatatypeDeclaration> node);
            virtual void visit(std::shared_ptr<ParametricDatatypeDeclaration> node);

            virtual void visit(std::shared_ptr<QualifiedConstructor> node);
            virtual void visit(std::shared_ptr<QualifiedPattern> node);
            virtual void visit(std::shared_ptr<MatchCase> node);

            virtual void visit(std::shared_ptr<QualifiedTerm> node);
            virtual void visit(std::shared_ptr<LetTerm> node);
            virtual void visit(std::shared_ptr<ForallTerm> node);
            virtual void visit(std::shared_ptr<ExistsTerm> node);
            virtual void visit(std::shared_ptr<MatchTerm> node);
            virtual void visit(std::shared_ptr<AnnotatedTerm> node);

            virtual void visit(std::shared_ptr<SortedVariable> node);
            virtual void visit(std::shared_ptr<VarBinding> node);

            virtual bool run (std::shared_ptr<AstNode> node) {
                ret = true;
                return wrappedVisit(node);
            }

            std::string getErrors();
        };
    }
}

#endif //PARSE_SMTLIB_AST_SYNTAX_CHECKER_H
