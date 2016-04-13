#ifndef PARSE_SMTLIB_AST_PREDICATE_UNFOLDER_H
#define PARSE_SMTLIB_AST_PREDICATE_UNFOLDER_H

#include <fstream>
#include "ast_visitor_extra.h"
#include "../ast/ast_fun.h"
#include "../ast/ast_interfaces.h"
#include "../ast/ast_term.h"

namespace smtlib {
    namespace ast {
        /* ============================ IPredicateUnfolderContext ============================= */
        class IPredicateUnfolderContext {
        public:
            virtual int getUnfoldLevel() = 0;
            virtual void setUnfoldLevel(int level) = 0;

            virtual bool isExistential() = 0;
            virtual void setExistential(bool existential) = 0;

            virtual std::string getOutputPath() = 0;
            virtual std::string setOutputPath(std::string output) = 0;

            virtual bool isCvcEmp() = 0;
            virtual void setCvcEmp(bool cvcEmp) = 0;
        };

        /* ============================= PredicateUnfolderContext ============================= */
        class PredicateUnfolderContext : public IPredicateUnfolderContext {
        private:
            int unfoldLevel;
            bool existential;
            std::string output;
            bool cvcEmp;

        public:
            inline PredicateUnfolderContext(int level, bool existential, std::string output, bool cvcEmp)
                    : unfoldLevel(level), existential(existential), output(output), cvcEmp(cvcEmp) {}

            virtual int getUnfoldLevel() { return unfoldLevel; }
            virtual void setUnfoldLevel(int level) { unfoldLevel = level; }

            virtual bool isExistential() { return existential; }
            virtual void setExistential(bool existential) { this->existential = existential; }

            virtual std::string getOutputPath() { return output; }
            virtual std::string setOutputPath(std::string output) { this->output = output; }

            virtual bool isCvcEmp() { return cvcEmp; }
            virtual void setCvcEmp(bool cvcEmp) { this->cvcEmp = cvcEmp; }
        };

        /* ================================ PredicateUnfolder ================================= */
        class PredicateUnfolder : public DummyAstVisitor2<std::shared_ptr<AstNode>, int>,
                                  public std::enable_shared_from_this<PredicateUnfolder> {
        private:
            std::shared_ptr<FunctionDefinition> currentDefinition;
            std::shared_ptr<Term> currentBaseCase;
            std::shared_ptr<ExistsTerm> currentRecCase;

            std::shared_ptr<IPredicateUnfolderContext> ctx;

            int findCounter;
            int prevFind;
            int *predLevelCounter;
            int predLevel;
            std::fstream output;

        public:
            inline PredicateUnfolder(std::shared_ptr<IPredicateUnfolderContext> ctx) : ctx(ctx) { }

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

            std::shared_ptr<AstNode> run(std::shared_ptr<AstNode> node) {
                return wrappedVisit(0, node);
            }
        };
    }
}

#endif //PARSE_SMTLIB_AST_PREDICATE_UNFOLDER_H
