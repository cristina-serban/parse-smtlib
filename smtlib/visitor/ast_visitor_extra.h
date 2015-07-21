#ifndef PARSE_SMTLIB_AST_VISITOR_EXTRA_H
#define PARSE_SMTLIB_AST_VISITOR_EXTRA_H

#include "ast_visitor.h"
#include "../ast/ast_abstract.h"
#include "../util/smt_logger.h"

namespace smtlib {
    namespace ast {
        template<class RetT>
        class AstVisitor1 : public virtual AstVisitor0 {
        protected:
            RetT ret;
            RetT wrappedVisit(std::shared_ptr<AstNode> node) {
                RetT oldRet = ret;
                visit0(node);
                RetT newRet = ret;
                ret = oldRet;
                return newRet;
            }
        public:
            virtual RetT run (std::shared_ptr<AstNode> node) {
                return wrappedVisit(node);
            }
        };

        template<class RetT, class ArgT>
        class AstVisitor2 : public virtual AstVisitor0 {
        protected:
            ArgT arg;
            RetT ret;

            RetT wrappedVisit(ArgT arg, std::shared_ptr<AstNode> node) {
                RetT oldRet = ret;
                this->arg = arg;
                visit0(node);
                RetT newRet = ret;
                ret = oldRet;
                return newRet;
            }
        public:
            virtual RetT run(ArgT arg, std::shared_ptr<AstNode> node) {
                return wrappedVisit(arg, node);
            }
        };

        template<class RetT>
        class DummyAstVisitor1 : public AstVisitor1<RetT>, public DummyVisitor0 {
        /*
        public:
            virtual void visit(std::shared_ptr<Attribute> node) { }
            virtual void visit(std::shared_ptr<CompAttributeValue> node) { }

            virtual void visit(std::shared_ptr<Symbol> node) { }
            virtual void visit(std::shared_ptr<Keyword> node) { }
            virtual void visit(std::shared_ptr<MetaSpecConstant> node) { }
            virtual void visit(std::shared_ptr<BooleanValue> node) { }
            virtual void visit(std::shared_ptr<PropLiteral> node) { }

            virtual void visit(std::shared_ptr<AssertCommand> node) { }
            virtual void visit(std::shared_ptr<CheckSatCommand> node) { }
            virtual void visit(std::shared_ptr<CheckSatAssumCommand> node) { }
            virtual void visit(std::shared_ptr<DeclareConstCommand> node) { }
            virtual void visit(std::shared_ptr<DeclareDatatypeCommand> node) { }
            virtual void visit(std::shared_ptr<DeclareDatatypesCommand> node) { }
            virtual void visit(std::shared_ptr<DeclareFunCommand> node) { }
            virtual void visit(std::shared_ptr<DeclareSortCommand> node) { }
            virtual void visit(std::shared_ptr<DefineFunCommand> node) { }
            virtual void visit(std::shared_ptr<DefineFunRecCommand> node) { }
            virtual void visit(std::shared_ptr<DefineFunsRecCommand> node) { }
            virtual void visit(std::shared_ptr<DefineSortCommand> node) { }
            virtual void visit(std::shared_ptr<EchoCommand> node) { }
            virtual void visit(std::shared_ptr<ExitCommand> node) { }
            virtual void visit(std::shared_ptr<GetAssertsCommand> node) { }
            virtual void visit(std::shared_ptr<GetAssignsCommand> node) { }
            virtual void visit(std::shared_ptr<GetInfoCommand> node) { }
            virtual void visit(std::shared_ptr<GetModelCommand> node) { }
            virtual void visit(std::shared_ptr<GetOptionCommand> node) { }
            virtual void visit(std::shared_ptr<GetProofCommand> node) { }
            virtual void visit(std::shared_ptr<GetUnsatAssumsCommand> node) { }
            virtual void visit(std::shared_ptr<GetUnsatCoreCommand> node) { }
            virtual void visit(std::shared_ptr<GetValueCommand> node) { }
            virtual void visit(std::shared_ptr<PopCommand> node) { }
            virtual void visit(std::shared_ptr<PushCommand> node) { }
            virtual void visit(std::shared_ptr<ResetCommand> node) { }
            virtual void visit(std::shared_ptr<ResetAssertsCommand> node) { }
            virtual void visit(std::shared_ptr<SetInfoCommand> node) { }
            virtual void visit(std::shared_ptr<SetLogicCommand> node) { }
            virtual void visit(std::shared_ptr<SetOptionCommand> node) { }

            virtual void visit(std::shared_ptr<FunctionDeclaration> node) { }
            virtual void visit(std::shared_ptr<FunctionDefinition> node) { }

            virtual void visit(std::shared_ptr<SimpleIdentifier> node) { }
            virtual void visit(std::shared_ptr<QualifiedIdentifier> node) { }

            virtual void visit(std::shared_ptr<DecimalLiteral> node) { }
            virtual void visit(std::shared_ptr<NumeralLiteral> node) { }
            virtual void visit(std::shared_ptr<StringLiteral> node) { }

            virtual void visit(std::shared_ptr<Logic> node) { }
            virtual void visit(std::shared_ptr<Theory> node) { }
            virtual void visit(std::shared_ptr<Script> node) { }

            virtual void visit(std::shared_ptr<Sort> node) { }

            virtual void visit(std::shared_ptr<CompSExpression> node) { }

            virtual void visit(std::shared_ptr<SortSymbolDeclaration> node) { }

            virtual void visit(std::shared_ptr<SpecConstFunDeclaration> node) { }
            virtual void visit(std::shared_ptr<MetaSpecConstFunDeclaration> node) { }
            virtual void visit(std::shared_ptr<SimpleFunDeclaration> node) { }
            virtual void visit(std::shared_ptr<ParametricFunDeclaration> node) { }

            virtual void visit(std::shared_ptr<SortDeclaration> node) { }
            virtual void visit(std::shared_ptr<SelectorDeclaration> node) { }
            virtual void visit(std::shared_ptr<ConstructorDeclaration> node) { }
            virtual void visit(std::shared_ptr<SimpleDatatypeDeclaration> node) { }
            virtual void visit(std::shared_ptr<ParametricDatatypeDeclaration> node) { }

            virtual void visit(std::shared_ptr<QualifiedConstructor> node) { }
            virtual void visit(std::shared_ptr<QualifiedPattern> node) { }
            virtual void visit(std::shared_ptr<MatchCase> node) { }

            virtual void visit(std::shared_ptr<QualifiedTerm> node) { }
            virtual void visit(std::shared_ptr<LetTerm> node) { }
            virtual void visit(std::shared_ptr<ForallTerm> node) { }
            virtual void visit(std::shared_ptr<ExistsTerm> node) { }
            virtual void visit(std::shared_ptr<MatchTerm> node) { }
            virtual void visit(std::shared_ptr<AnnotatedTerm> node) { }

            virtual void visit(std::shared_ptr<SortedVariable> node) { }
            virtual void visit(std::shared_ptr<VarBinding> node) { }
        */
        };

        template<class RetT, class ArgT>
        class DummyAstVisitor2 : public AstVisitor2<RetT, ArgT>, public DummyVisitor0 {
        /*
        public:
            virtual void visit(std::shared_ptr<Attribute> node) { }
            virtual void visit(std::shared_ptr<CompAttributeValue> node) { }

            virtual void visit(std::shared_ptr<Symbol> node) { }
            virtual void visit(std::shared_ptr<Keyword> node) { }
            virtual void visit(std::shared_ptr<MetaSpecConstant> node) { }
            virtual void visit(std::shared_ptr<BooleanValue> node) { }
            virtual void visit(std::shared_ptr<PropLiteral> node) { }

            virtual void visit(std::shared_ptr<AssertCommand> node) { }
            virtual void visit(std::shared_ptr<CheckSatCommand> node) { }
            virtual void visit(std::shared_ptr<CheckSatAssumCommand> node) { }
            virtual void visit(std::shared_ptr<DeclareConstCommand> node) { }
            virtual void visit(std::shared_ptr<DeclareDatatypeCommand> node) { }
            virtual void visit(std::shared_ptr<DeclareDatatypesCommand> node) { }
            virtual void visit(std::shared_ptr<DeclareFunCommand> node) { }
            virtual void visit(std::shared_ptr<DeclareSortCommand> node) { }
            virtual void visit(std::shared_ptr<DefineFunCommand> node) { }
            virtual void visit(std::shared_ptr<DefineFunRecCommand> node) { }
            virtual void visit(std::shared_ptr<DefineFunsRecCommand> node) { }
            virtual void visit(std::shared_ptr<DefineSortCommand> node) { }
            virtual void visit(std::shared_ptr<EchoCommand> node) { }
            virtual void visit(std::shared_ptr<ExitCommand> node) { }
            virtual void visit(std::shared_ptr<GetAssertsCommand> node) { }
            virtual void visit(std::shared_ptr<GetAssignsCommand> node) { }
            virtual void visit(std::shared_ptr<GetInfoCommand> node) { }
            virtual void visit(std::shared_ptr<GetModelCommand> node) { }
            virtual void visit(std::shared_ptr<GetOptionCommand> node) { }
            virtual void visit(std::shared_ptr<GetProofCommand> node) { }
            virtual void visit(std::shared_ptr<GetUnsatAssumsCommand> node) { }
            virtual void visit(std::shared_ptr<GetUnsatCoreCommand> node) { }
            virtual void visit(std::shared_ptr<GetValueCommand> node) { }
            virtual void visit(std::shared_ptr<PopCommand> node) { }
            virtual void visit(std::shared_ptr<PushCommand> node) { }
            virtual void visit(std::shared_ptr<ResetCommand> node) { }
            virtual void visit(std::shared_ptr<ResetAssertsCommand> node) { }
            virtual void visit(std::shared_ptr<SetInfoCommand> node) { }
            virtual void visit(std::shared_ptr<SetLogicCommand> node) { }
            virtual void visit(std::shared_ptr<SetOptionCommand> node) { }

            virtual void visit(std::shared_ptr<FunctionDeclaration> node) { }
            virtual void visit(std::shared_ptr<FunctionDefinition> node) { }

            virtual void visit(std::shared_ptr<SimpleIdentifier> node) { }
            virtual void visit(std::shared_ptr<QualifiedIdentifier> node) { }

            virtual void visit(std::shared_ptr<DecimalLiteral> node) { }
            virtual void visit(std::shared_ptr<NumeralLiteral> node) { }
            virtual void visit(std::shared_ptr<StringLiteral> node) { }

            virtual void visit(std::shared_ptr<Logic> node) { }
            virtual void visit(std::shared_ptr<Theory> node) { }
            virtual void visit(std::shared_ptr<Script> node) { }

            virtual void visit(std::shared_ptr<Sort> node) { }

            virtual void visit(std::shared_ptr<CompSExpression> node) { }

            virtual void visit(std::shared_ptr<SortSymbolDeclaration> node) { }

            virtual void visit(std::shared_ptr<SpecConstFunDeclaration> node) { }
            virtual void visit(std::shared_ptr<MetaSpecConstFunDeclaration> node) { }
            virtual void visit(std::shared_ptr<SimpleFunDeclaration> node) { }
            virtual void visit(std::shared_ptr<ParametricFunDeclaration> node) { }

            virtual void visit(std::shared_ptr<SortDeclaration> node) { }
            virtual void visit(std::shared_ptr<SelectorDeclaration> node) { }
            virtual void visit(std::shared_ptr<ConstructorDeclaration> node) { }
            virtual void visit(std::shared_ptr<SimpleDatatypeDeclaration> node) { }
            virtual void visit(std::shared_ptr<ParametricDatatypeDeclaration> node) { }

            virtual void visit(std::shared_ptr<QualifiedConstructor> node) { }
            virtual void visit(std::shared_ptr<QualifiedPattern> node) { }
            virtual void visit(std::shared_ptr<MatchCase> node) { }

            virtual void visit(std::shared_ptr<QualifiedTerm> node) { }
            virtual void visit(std::shared_ptr<LetTerm> node) { }
            virtual void visit(std::shared_ptr<ForallTerm> node) { }
            virtual void visit(std::shared_ptr<ExistsTerm> node) { }
            virtual void visit(std::shared_ptr<MatchTerm> node) { }
            virtual void visit(std::shared_ptr<AnnotatedTerm> node) { }

            virtual void visit(std::shared_ptr<SortedVariable> node) { }
            virtual void visit(std::shared_ptr<VarBinding> node) { }
            */
        };
    }
}

#endif //PARSE_SMTLIB_AST_VISITOR_EXTRA_H