#include "ast_visitor.h"
#include "../ast/ast_attribute.h"
#include "../ast/ast_command.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_theory.h"
#include "../ast/ast_script.h"
#include "../ast/ast_sexp.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_term.h"

using namespace smtlib::ast;

void AstVisitor0::visit0(std::shared_ptr<AstNode> node) {
    if (node == NULL) {
        return;
    }
    node->accept(this);
}

void DummyAstVisitor0::visit(std::shared_ptr<Attribute> node) {
    visit0(node->getKeyword());
    visit0(node->getValue());
}

void DummyAstVisitor0::visit(std::shared_ptr<CompAttributeValue> node) {
    visit0(node->getValues());
}

void DummyAstVisitor0::visit(std::shared_ptr<Symbol> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<Keyword> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<MetaSpecConstant> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<BooleanValue> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<PropLiteral> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<AssertCommand> node) {
    visit0(node->getTerm());
}

void DummyAstVisitor0::visit(std::shared_ptr<CheckSatCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<CheckSatAssumCommand> node) {
    visit0(node->getAssumptions());
}

void DummyAstVisitor0::visit(std::shared_ptr<DeclareConstCommand> node) {
    visit0(node->getSymbol());
    visit0(node->getSort());
}

void DummyAstVisitor0::visit(std::shared_ptr<DeclareDatatypeCommand> node) {
    visit0(node->getSymbol());
    visit0(node->getDeclaration());
}

void DummyAstVisitor0::visit(std::shared_ptr<DeclareDatatypesCommand> node) {
    visit0(node->getDeclarations());
}

void DummyAstVisitor0::visit(std::shared_ptr<DeclareFunCommand> node) {
    visit0(node->getSymbol());
    visit0(node->getParams());
    visit0(node->getSort());
}

void DummyAstVisitor0::visit(std::shared_ptr<DeclareSortCommand> node) {
    visit0(node->getSymbol());
}

void DummyAstVisitor0::visit(std::shared_ptr<DefineFunCommand> node) {
    visit0(node->getDefinition());
}

void DummyAstVisitor0::visit(std::shared_ptr<DefineFunRecCommand> node) {
    visit0(node->getDefinition());
}

void DummyAstVisitor0::visit(std::shared_ptr<DefineFunsRecCommand> node) {
    visit0(node->getDeclarations());
    visit0(node->getBodies());
}

void DummyAstVisitor0::visit(std::shared_ptr<DefineSortCommand> node) {
    visit0(node->getSymbol());
    visit0(node->getParams());
    visit0(node->getSort());
}

void DummyAstVisitor0::visit(std::shared_ptr<EchoCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<ExitCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<GetAssertsCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<GetAssignsCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<GetInfoCommand> node) {
    visit0(node->getFlag());
}

void DummyAstVisitor0::visit(std::shared_ptr<GetModelCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<GetOptionCommand> node) {
    visit0(node->getOption());
}

void DummyAstVisitor0::visit(std::shared_ptr<GetProofCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<GetUnsatAssumsCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<GetUnsatCoreCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<GetValueCommand> node) {
    visit0(node->getTerms());
}

void DummyAstVisitor0::visit(std::shared_ptr<PopCommand> node) {
    visit0(node->getNumeral());
}

void DummyAstVisitor0::visit(std::shared_ptr<PushCommand> node) {
    visit0(node->getNumeral());
}

void DummyAstVisitor0::visit(std::shared_ptr<ResetCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<ResetAssertsCommand> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<SetInfoCommand> node) {
    visit0(node->getInfo());
}

void DummyAstVisitor0::visit(std::shared_ptr<SetLogicCommand> node) {
    visit0(node->getLogic());
}

void DummyAstVisitor0::visit(std::shared_ptr<SetOptionCommand> node) {
    visit0(node->getOption());
}

void DummyAstVisitor0::visit(std::shared_ptr<FunctionDeclaration> node) {
    visit0(node->getSymbol());
    visit0(node->getParams());
    visit0(node->getSort());
}

void DummyAstVisitor0::visit(std::shared_ptr<FunctionDefinition> node) {
    visit0(node->getSignature());
    visit0(node->getBody());
}

void DummyAstVisitor0::visit(std::shared_ptr<SimpleIdentifier> node) {
    visit0(node->getSymbol());
}

void DummyAstVisitor0::visit(std::shared_ptr<QualifiedIdentifier> node) {
    visit0(node->getIdentifier());
    visit0(node->getSort());
}

void DummyAstVisitor0::visit(std::shared_ptr<DecimalLiteral> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<NumeralLiteral> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<StringLiteral> node) { }

void DummyAstVisitor0::visit(std::shared_ptr<Logic> node) {
    visit0(node->getName());
    visit0(node->getAttributes());
}

void DummyAstVisitor0::visit(std::shared_ptr<Theory> node) {
    visit0(node->getName());
    visit0(node->getAttributes());
}

void DummyAstVisitor0::visit(std::shared_ptr<Script> node) {
    visit0(node->getCommands());
}

void DummyAstVisitor0::visit(std::shared_ptr<Sort> node) {
    visit0(node->getIdentifier());
    visit0(node->getArgs());
}

void DummyAstVisitor0::visit(std::shared_ptr<CompSExpression> node) {
    visit0(node->getExpressions());
}

void DummyAstVisitor0::visit(std::shared_ptr<SortSymbolDeclaration> node) {
    visit0(node->getIdentifier());
    visit0(node->getArity());
    visit0(node->getAttributes());
}

void DummyAstVisitor0::visit(std::shared_ptr<SortDeclaration> node) {
    visit0(node->getSymbol());
    visit0(node->getArity());
}

void DummyAstVisitor0::visit(std::shared_ptr<SelectorDeclaration> node) {
    visit0(node->getSymbol());
    visit0(node->getSort());
}

void DummyAstVisitor0::visit(std::shared_ptr<ConstructorDeclaration> node) {
    visit0(node->getSymbol());
    visit0(node->getSelectors());
}

void DummyAstVisitor0::visit(std::shared_ptr<SimpleDatatypeDeclaration> node) {
    visit0(node->getConstructors());
}

void DummyAstVisitor0::visit(std::shared_ptr<ParametricDatatypeDeclaration> node) {
    visit0(node->getConstructors());
    visit0(node->getParams());
}

void DummyAstVisitor0::visit(std::shared_ptr<QualifiedConstructor> node) {
    visit0(node->getSymbol());
    visit0(node->getSort());
}

void DummyAstVisitor0::visit(std::shared_ptr<QualifiedPattern> node) {
    visit0(node->getConstructor());
    visit0(node->getSymbols());
}

void DummyAstVisitor0::visit(std::shared_ptr<MatchCase> node) {
    visit0(node->getPattern());
    visit0(node->getTerm());
}

void DummyAstVisitor0::visit(std::shared_ptr<SpecConstFunDeclaration> node) {
    visit0(node->getConstant());
    visit0(node->getSort());
    visit0(node->getAttributes());
}

void DummyAstVisitor0::visit(std::shared_ptr<MetaSpecConstFunDeclaration> node) {
    visit0(node->getConstant());
    visit0(node->getSort());
    visit0(node->getAttributes());
}

void DummyAstVisitor0::visit(std::shared_ptr<SimpleFunDeclaration> node) {
    visit0(node->getIdentifier());
    visit0(node->getSignature());
    visit0(node->getAttributes());
}

void DummyAstVisitor0::visit(std::shared_ptr<ParametricFunDeclaration> node) {
    visit0(node->getParams());
    visit0(node->getIdentifier());
    visit0(node->getSignature());
    visit0(node->getAttributes());
}

void DummyAstVisitor0::visit(std::shared_ptr<QualifiedTerm> node) {
    visit0(node->getIdentifier());
    visit0(node->getTerms());
}

void DummyAstVisitor0::visit(std::shared_ptr<LetTerm> node) {
    visit0(node->getBindings());
    visit0(node->getTerm());
}

void DummyAstVisitor0::visit(std::shared_ptr<ForallTerm> node) {
    visit0(node->getBindings());
    visit0(node->getTerm());
}

void DummyAstVisitor0::visit(std::shared_ptr<ExistsTerm> node) {
    visit0(node->getBindings());
    visit0(node->getTerm());
}

void DummyAstVisitor0::visit(std::shared_ptr<MatchTerm> node) {
    visit0(node->getTerm());
    visit0(node->getCases());
}

void DummyAstVisitor0::visit(std::shared_ptr<AnnotatedTerm> node) {
    visit0(node->getTerm());
    visit0(node->getAttributes());
}

void DummyAstVisitor0::visit(std::shared_ptr<SortedVariable> node) {
    visit0(node->getSymbol());
    visit0(node->getSort());
}

void DummyAstVisitor0::visit(std::shared_ptr<VarBinding> node) {
    visit0(node->getSymbol());
    visit0(node->getTerm());
}
