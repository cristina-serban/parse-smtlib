#ifndef PARSE_SMTLIB_AST_VISITOR_H
#define PARSE_SMTLIB_AST_VISITOR_H

#include "../ast/ast_classes.h"
#include <memory>

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
        
        class DummyVisitor0 : public AstVisitor0 {
        public:
            virtual void visit(Attribute const *node) { }
            virtual void visit(CompoundAttributeValue const *node) { }

            virtual void visit(Symbol const *node) { }
            virtual void visit(Keyword const *node) { }
            virtual void visit(MetaSpecConstant const *node) { }
            virtual void visit(BooleanValue const *node) { }
            virtual void visit(PropLiteral const *node) { }

            virtual void visit(AssertCommand const *node) { }
            virtual void visit(CheckSatCommand const *node) { }
            virtual void visit(CheckSatAssumCommand const *node) { }
            virtual void visit(DeclareConstCommand const *node) { }
            virtual void visit(DeclareFunCommand const *node) { }
            virtual void visit(DeclareSortCommand const *node) { }
            virtual void visit(DefineFunCommand const *node) { }
            virtual void visit(DefineFunRecCommand const *node) { }
            virtual void visit(DefineFunsRecCommand const *node) { }
            virtual void visit(DefineSortCommand const *node) { }
            virtual void visit(EchoCommand const *node) { }
            virtual void visit(ExitCommand const *node) { }
            virtual void visit(GetAssertsCommand const *node) { }
            virtual void visit(GetAssignsCommand const *node) { }
            virtual void visit(GetInfoCommand const *node) { }
            virtual void visit(GetModelCommand const *node) { }
            virtual void visit(GetOptionCommand const *node) { }
            virtual void visit(GetProofCommand const *node) { }
            virtual void visit(GetUnsatAssumsCommand const *node) { }
            virtual void visit(GetUnsatCoreCommand const *node) { }
            virtual void visit(GetValueCommand const *node) { }
            virtual void visit(PopCommand const *node) { }
            virtual void visit(PushCommand const *node) { }
            virtual void visit(ResetCommand const *node) { }
            virtual void visit(ResetAssertsCommand const *node) { }
            virtual void visit(SetInfoCommand const *node) { }
            virtual void visit(SetLogicCommand const *node) { }
            virtual void visit(SetOptionCommand const *node) { }

            virtual void visit(FunctionDeclaration const *node) { }
            virtual void visit(FunctionDefinition const *node) { }

            virtual void visit(Identifier const *node) { }
            virtual void visit(QualifiedIdentifier const *node) { }

            virtual void visit(DecimalLiteral const *node) { }
            virtual void visit(NumeralLiteral const *node) { }
            virtual void visit(StringLiteral const *node) { }

            virtual void visit(Logic const *node) { }
            virtual void visit(Theory const *node) { }
            virtual void visit(Script const *node) { }

            virtual void visit(Sort const *node) { }

            virtual void visit(CompSExpression const *node) { }

            virtual void visit(SortSymbolDeclaration const *node) { }

            virtual void visit(SpecConstFunDeclaration const *node) { }
            virtual void visit(MetaSpecConstFunDeclaration const *node) { }
            virtual void visit(IdentifierFunDeclaration const *node) { }
            virtual void visit(ParametricFunDeclaration const *node) { }

            virtual void visit(QualifiedTerm const *node) { }
            virtual void visit(LetTerm const *node) { }
            virtual void visit(ForallTerm const *node) { }
            virtual void visit(ExistsTerm const *node) { }
            virtual void visit(AnnotatedTerm const *node) { }

            virtual void visit(SortedVariable const *node) { }
            virtual void visit(VarBinding const *node) { }
        };
    }
}

#endif //PARSE_SMTLIB_AST_VISITOR_H
