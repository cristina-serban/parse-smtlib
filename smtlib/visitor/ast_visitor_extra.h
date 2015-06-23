#ifndef PARSE_SMTLIB_AST_VISITOR_EXTRA_H
#define PARSE_SMTLIB_AST_VISITOR_EXTRA_H

#include "ast_visitor.h"
#include "../ast/ast_abstract.h"

namespace smtlib {
    namespace ast {
        template<class RetT>
        class AstVisitor1 : public AstVisitor0 {
        protected:
            RetT ret;

            RetT wrappedVisit(AstNode const *node) {
                node->accept(this);
                return this->ret;
            }
        public:
            virtual RetT run (AstNode const *node) {
                return wrappedVisit(node);
            }
        };

        template<class RetT, class ArgT>
        class AstVisitor2 : public AstVisitor0 {
        protected:
            ArgT arg;
            RetT ret;

            RetT wrappedVisit(ArgT arg, AstNode const *node) {
                this->arg = arg;
                node->accept(this);
                return this->ret;
            }
        public:
            virtual RetT run(ArgT arg, AstNode const *node);
        };

        template<class RetT>
        class DummyAstVisitor1 : public AstVisitor1<RetT> {
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

        template<class RetT, class ArgT>
        class DummyAstVisitor2 : public AstVisitor2<RetT, ArgT> {
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

#endif //PARSE_SMTLIB_AST_VISITOR_EXTRA_H
