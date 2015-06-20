#ifndef PARSE_SMTLIB_AST_SYNTAX_CHECKER_H
#define PARSE_SMTLIB_AST_SYNTAX_CHECKER_H

#include <visitor/ast_visitor_extra.h>
#include <regex>
#include <string>
#include <vector>

namespace smtlib {
    namespace ast {
        class SyntaxChecker : public AstVisitor1<bool> {
        private:
            struct SyntaxCheckError {
                std::vector<std::string> messages;
                AstNode const *node;
            };

            std::string file;
            std::vector<std::shared_ptr<SyntaxCheckError>> errors;

            const std::regex regexSymbol = std::regex("^([a-zA-Z+\\-/*=%?!.$_~&^<>@][a-zA-Z0-9+\\-/*=%?!.$_~&^<>@]*)|(\\|[\\x20-\\x5B\\x5D-\\x7B\\x7D\\x7E\\xA0-\\xFF\\x09\\r\\n \\xA0]*\\|)$");
            const std::regex regexKeyword = std::regex ("^:([a-zA-Z+\\-/*=%?!.$_~&^<>@][a-zA-Z0-9+\\-/*=%?!.$_~&^<>@]*)|(\\|[\\x20-\\x5B\\x5D-\\x7B\\x7D\\x7E\\xA0-\\xFF\\x09\\r\\n \\xA0]*\\|)$");

            std::shared_ptr<SyntaxCheckError> addError(std::string message, AstNode const *node,
                                                       std::shared_ptr<SyntaxCheckError> err);
        public:
            virtual void visit(Attribute const *node);
            virtual void visit(CompoundAttributeValue const *node);

            virtual void visit(Symbol const *node);
            virtual void visit(Keyword const *node);
            virtual void visit(MetaSpecConstant const *node);
            virtual void visit(BooleanValue const *node);
            virtual void visit(PropLiteral const *node);

            virtual void visit(AssertCommand const *node);
            virtual void visit(CheckSatCommand const *node);
            virtual void visit(CheckSatAssumCommand const *node);
            virtual void visit(DeclareConstCommand const *node);
            virtual void visit(DeclareFunCommand const *node);
            virtual void visit(DeclareSortCommand const *node);
            virtual void visit(DefineFunCommand const *node);
            virtual void visit(DefineFunRecCommand const *node);
            virtual void visit(DefineFunsRecCommand const *node);
            virtual void visit(DefineSortCommand const *node);
            virtual void visit(EchoCommand const *node);
            virtual void visit(ExitCommand const *node);
            virtual void visit(GetAssertsCommand const *node);
            virtual void visit(GetAssignsCommand const *node);
            virtual void visit(GetInfoCommand const *node);
            virtual void visit(GetModelCommand const *node);
            virtual void visit(GetOptionCommand const *node);
            virtual void visit(GetProofCommand const *node);
            virtual void visit(GetUnsatAssumsCommand const *node);
            virtual void visit(GetUnsatCoreCommand const *node);
            virtual void visit(GetValueCommand const *node);
            virtual void visit(PopCommand const *node);
            virtual void visit(PushCommand const *node);
            virtual void visit(ResetCommand const *node);
            virtual void visit(ResetAssertsCommand const *node);
            virtual void visit(SetInfoCommand const *node);
            virtual void visit(SetLogicCommand const *node);
            virtual void visit(SetOptionCommand const *node);

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

            virtual bool run (AstNode const *node) {
                ret = true;
                return wrappedVisit(node);
            }

            void setFilePath(std::string filePath) {
                file = filePath;
            }

            std::string getErrors();
        };
    }
}

#endif //PARSE_SMTLIB_AST_SYNTAX_CHECKER_H
