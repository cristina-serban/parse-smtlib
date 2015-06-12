#ifndef PARSE_SMTLIB_AST_VISITOR_H
#define PARSE_SMTLIB_AST_VISITOR_H

#include <memory>
#include <ast/ast_classes.h>

namespace smtlib {
    namespace ast {
        class AstVisitor0 {
        public:
            virtual void visit(Attribute const *node) = 0;
            virtual void visit(CompoundAttributeValue const *node) = 0;

            virtual void visit(Symbol const *node) = 0;
            virtual void visit(Keyword const *node) = 0;
            virtual void visit(MetaSpecConstant const *node) = 0;
            virtual void visit(BooleanValue const *node) = 0;
            virtual void visit(PropLiteral const *node) = 0;

            virtual void visit(AssertCommand const *node) = 0;
            virtual void visit(CheckSatCommand const *node) = 0;
            virtual void visit(CheckSatAssumCommand const *node) = 0;
            virtual void visit(DeclareConstCommand const *node) = 0;
            virtual void visit(DeclareFunCommand const *node) = 0;
            virtual void visit(DeclareSortCommand const *node) = 0;
            virtual void visit(DefineFunCommand const *node) = 0;
            virtual void visit(DefineFunRecCommand const *node) = 0;
            virtual void visit(DefineFunsRecCommand const *node) = 0;
            virtual void visit(DefineSortCommand const *node) = 0;
            virtual void visit(EchoCommand const *node) = 0;
            virtual void visit(ExitCommand const *node) = 0;
            virtual void visit(GetAssertsCommand const *node) = 0;
            virtual void visit(GetAssignsCommand const *node) = 0;
            virtual void visit(GetInfoCommand const *node) = 0;
            virtual void visit(GetModelCommand const *node) = 0;
            virtual void visit(GetOptionCommand const *node) = 0;
            virtual void visit(GetProofCommand const *node) = 0;
            virtual void visit(GetUnsatAssumsCommand const *node) = 0;
            virtual void visit(GetUnsatCoreCommand const *node) = 0;
            virtual void visit(GetValueCommand const *node) = 0;
            virtual void visit(PopCommand const *node) = 0;
            virtual void visit(PushCommand const *node) = 0;
            virtual void visit(ResetCommand const *node) = 0;
            virtual void visit(ResetAssertsCommand const *node) = 0;
            virtual void visit(SetInfoCommand const *node) = 0;
            virtual void visit(SetLogicCommand const *node) = 0;
            virtual void visit(SetOptionCommand const *node) = 0;

            virtual void visit(FunctionDeclaration const *node) = 0;
            virtual void visit(FunctionDefinition const *node) = 0;

            virtual void visit(Identifier const *node) = 0;
            virtual void visit(QualifiedIdentifier const *node) = 0;

            virtual void visit(DecimalLiteral const *node) = 0;
            virtual void visit(NumeralLiteral const *node) = 0;
            virtual void visit(StringLiteral const *node) = 0;

            virtual void visit(Logic const *node) = 0;
            virtual void visit(Theory const *node) = 0;
            virtual void visit(Script const *node) = 0;

            virtual void visit(Sort const *node) = 0;

            virtual void visit(CompSExpression const *node) = 0;

            virtual void visit(SortSymbolDeclaration const *node) = 0;

            virtual void visit(SpecConstFunDeclaration const *node) = 0;
            virtual void visit(MetaSpecConstFunDeclaration const *node) = 0;
            virtual void visit(IdentifierFunDeclaration const *node) = 0;
            virtual void visit(ParametricFunDeclaration const *node) = 0;

            virtual void visit(QualifiedTerm const *node) = 0;
            virtual void visit(LetTerm const *node) = 0;
            virtual void visit(ForallTerm const *node) = 0;
            virtual void visit(ExistsTerm const *node) = 0;
            virtual void visit(AnnotatedTerm const *node) = 0;

            virtual void visit(SortedVariable const *node) = 0;
            virtual void visit(VarBinding const *node) = 0;
        };
    }
}

#endif //PARSE_SMTLIB_AST_VISITOR_H
