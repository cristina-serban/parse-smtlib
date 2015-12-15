#include "ast_node_duplicator.h"
#include "../ast/ast_datatype.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_sexp.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_term.h"
#include "../ast/ast_theory.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

void NodeDuplicator::visit(shared_ptr<Attribute> node) {
    shared_ptr<Keyword> newKeyword = dynamic_pointer_cast<Keyword>(wrappedVisit(node->getKeyword()));
    shared_ptr<AttributeValue> newValue = dynamic_pointer_cast<AttributeValue>(wrappedVisit(node->getValue()));

    shared_ptr<Attribute> newNode = make_shared<Attribute>(newKeyword, newValue);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<CompAttributeValue> node) {
    vector<shared_ptr<AttributeValue>> newValues;
    for (shared_ptr<AttributeValue> value : node->getValues()) {
        newValues.push_back(dynamic_pointer_cast<AttributeValue>(wrappedVisit(value)));
    }

    shared_ptr<CompAttributeValue> newNode = make_shared<CompAttributeValue>(newValues);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<Symbol> node) {
    shared_ptr<Symbol> newNode = make_shared<Symbol>(node->getValue());

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<Keyword> node) {
    shared_ptr<Keyword> newNode = make_shared<Keyword>(node->getValue());

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<MetaSpecConstant> node) {
    shared_ptr<MetaSpecConstant> newNode = make_shared<MetaSpecConstant>(node->getType());

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<BooleanValue> node) {
    shared_ptr<BooleanValue> newNode = make_shared<BooleanValue>(node->getValue());

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<PropLiteral> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));

    shared_ptr<PropLiteral> newNode = make_shared<PropLiteral>(newSymbol, node->isNegated());

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<AssertCommand> node) {
    shared_ptr<Term> newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->getTerm()));

    shared_ptr<AssertCommand> newNode = make_shared<AssertCommand>(newTerm);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<CheckSatCommand> node) {
    shared_ptr<CheckSatCommand> newNode = make_shared<CheckSatCommand>();

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<CheckSatAssumCommand> node) {
    vector<shared_ptr<PropLiteral>> newAssums;
    for (shared_ptr<PropLiteral> assum : node->getAssumptions()) {
        newAssums.push_back(dynamic_pointer_cast<PropLiteral>(wrappedVisit(assum)));
    }

    shared_ptr<CheckSatAssumCommand> newNode = make_shared<CheckSatAssumCommand>(newAssums);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<DeclareConstCommand> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));
    shared_ptr<Sort> newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->getSort()));

    shared_ptr<DeclareConstCommand> newNode = make_shared<DeclareConstCommand>(newSymbol, newSort);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<DeclareDatatypeCommand> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));
    shared_ptr<DatatypeDeclaration> newDecl = dynamic_pointer_cast<DatatypeDeclaration>(wrappedVisit(node->getDeclaration()));

    shared_ptr<DeclareDatatypeCommand> newNode = make_shared<DeclareDatatypeCommand>(newSymbol, newDecl);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<DeclareDatatypesCommand> node) {
    vector<shared_ptr<SortDeclaration>> newSorts;
    for (shared_ptr<SortDeclaration> sort : node->getSorts()) {
        newSorts.push_back(dynamic_pointer_cast<SortDeclaration>(wrappedVisit(sort)));
    }

    vector<shared_ptr<DatatypeDeclaration>> newDecls;
    for (shared_ptr<DatatypeDeclaration> decl : node->getDeclarations()) {
        newDecls.push_back(dynamic_pointer_cast<DatatypeDeclaration>(wrappedVisit(decl)));
    }

    shared_ptr<DeclareDatatypesCommand> newNode = make_shared<DeclareDatatypesCommand>(newSorts, newDecls);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<DeclareFunCommand> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));

    vector<shared_ptr<Sort>> newParams;
    for (shared_ptr<Sort> param : node->getParams()) {
        newParams.push_back(dynamic_pointer_cast<Sort>(wrappedVisit(param)));
    }

    shared_ptr<Sort> newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->getSort()));

    shared_ptr<DeclareFunCommand> newNode = make_shared<DeclareFunCommand>(newSymbol, newParams, newSort);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<DeclareSortCommand> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));
    shared_ptr<NumeralLiteral> newArity = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->getArity()));

    shared_ptr<DeclareSortCommand> newNode = make_shared<DeclareSortCommand>(newSymbol, newArity);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<DefineFunCommand> node) {
    shared_ptr<FunctionDefinition> newDef = dynamic_pointer_cast<FunctionDefinition>(wrappedVisit(node->getDefinition()));

    shared_ptr<DefineFunCommand> newNode = make_shared<DefineFunCommand>(newDef);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<DefineFunRecCommand> node) {
    shared_ptr<FunctionDefinition> newDef = dynamic_pointer_cast<FunctionDefinition>(wrappedVisit(node->getDefinition()));

    shared_ptr<DefineFunRecCommand> newNode = make_shared<DefineFunRecCommand>(newDef);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<DefineFunsRecCommand> node) {
    vector<shared_ptr<FunctionDeclaration>> newDecls;
    for (shared_ptr<FunctionDeclaration> sort : node->getDeclarations()) {
        newDecls.push_back(dynamic_pointer_cast<FunctionDeclaration>(wrappedVisit(sort)));
    }

    vector<shared_ptr<Term>> newBodies;
    for (shared_ptr<Term> decl : node->getBodies()) {
        newBodies.push_back(dynamic_pointer_cast<Term>(wrappedVisit(decl)));
    }

    shared_ptr<DefineFunsRecCommand> newNode = make_shared<DefineFunsRecCommand>(newDecls, newBodies);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<DefineSortCommand> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));

    vector<shared_ptr<Symbol>> newParams;
    for (shared_ptr<Symbol> param : node->getParams()) {
        newParams.push_back(dynamic_pointer_cast<Symbol>(wrappedVisit(param)));
    }

    shared_ptr<Sort> newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->getSort()));

    shared_ptr<DefineSortCommand> newNode = make_shared<DefineSortCommand>(newSymbol, newParams, newSort);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<EchoCommand> node) {
    shared_ptr<EchoCommand> newNode = make_shared<EchoCommand>(node->getMessage());

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<ExitCommand> node) {
    shared_ptr<ExitCommand> newNode = make_shared<ExitCommand>();

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<GetAssertsCommand> node) {
    shared_ptr<GetAssertsCommand> newNode = make_shared<GetAssertsCommand>();

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<GetAssignsCommand> node) {
    shared_ptr<GetAssignsCommand> newNode = make_shared<GetAssignsCommand>();

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<GetInfoCommand> node) {
    shared_ptr<Keyword> newFlag = dynamic_pointer_cast<Keyword>(wrappedVisit(node->getFlag()));

    shared_ptr<GetInfoCommand> newNode = make_shared<GetInfoCommand>(newFlag);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<GetModelCommand> node) {
    shared_ptr<GetModelCommand> newNode = make_shared<GetModelCommand>();

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<GetOptionCommand> node) {
    shared_ptr<Keyword> newOpt = dynamic_pointer_cast<Keyword>(wrappedVisit(node->getOption()));

    shared_ptr<GetOptionCommand> newNode = make_shared<GetOptionCommand>(newOpt);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<GetProofCommand> node) {
    shared_ptr<GetProofCommand> newNode = make_shared<GetProofCommand>();

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<GetUnsatAssumsCommand> node) {
    shared_ptr<GetUnsatAssumsCommand> newNode = make_shared<GetUnsatAssumsCommand>();

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<GetUnsatCoreCommand> node) {
    shared_ptr<GetUnsatCoreCommand> newNode = make_shared<GetUnsatCoreCommand>();

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<GetValueCommand> node) {
    vector<shared_ptr<Term>> newTerms;
    for (shared_ptr<Term> param : node->getTerms()) {
        newTerms.push_back(dynamic_pointer_cast<Term>(wrappedVisit(param)));
    }

    shared_ptr<GetValueCommand> newNode = make_shared<GetValueCommand>(newTerms);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<PopCommand> node) {
    shared_ptr<NumeralLiteral> newNumeral = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->getNumeral()));

    shared_ptr<PopCommand> newNode = make_shared<PopCommand>(newNumeral);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<PushCommand> node) {
    shared_ptr<NumeralLiteral> newNumeral = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->getNumeral()));

    shared_ptr<PushCommand> newNode = make_shared<PushCommand>(newNumeral);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<ResetCommand> node) {
    shared_ptr<ResetCommand> newNode = make_shared<ResetCommand>();

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<ResetAssertsCommand> node) {
    shared_ptr<ResetAssertsCommand> newNode = make_shared<ResetAssertsCommand>();

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SetInfoCommand> node) {
    shared_ptr<Attribute> newAttr = dynamic_pointer_cast<Attribute>(wrappedVisit(node->getInfo()));

    shared_ptr<SetInfoCommand> newNode = make_shared<SetInfoCommand>(newAttr);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SetLogicCommand> node) {
    shared_ptr<Symbol> newLogic = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getLogic()));

    shared_ptr<SetLogicCommand> newNode = make_shared<SetLogicCommand>(newLogic);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SetOptionCommand> node) {
    shared_ptr<Attribute> newOpt = dynamic_pointer_cast<Attribute>(wrappedVisit(node->getOption()));

    shared_ptr<SetOptionCommand> newNode = make_shared<SetOptionCommand>(newOpt);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
    newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<FunctionDeclaration> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));

    vector<shared_ptr<SortedVariable>> newParams;
    for (shared_ptr<SortedVariable> param : node->getParams()) {
        newParams.push_back(dynamic_pointer_cast<SortedVariable>(wrappedVisit(param)));
    }

    shared_ptr<Sort> newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->getSort()));

    shared_ptr<FunctionDeclaration> newNode = make_shared<FunctionDeclaration>(newSymbol, newParams, newSort);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<FunctionDefinition> node) {
    shared_ptr<FunctionDeclaration> newSignature =
            dynamic_pointer_cast<FunctionDeclaration>(wrappedVisit(node->getSignature()));
    shared_ptr<Term> newBody = dynamic_pointer_cast<Term>(wrappedVisit(node->getBody()));

    shared_ptr<FunctionDefinition> newNode = make_shared<FunctionDefinition>(newSignature, newBody);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SimpleIdentifier> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));

    shared_ptr<SimpleIdentifier> newNode = make_shared<SimpleIdentifier>(newSymbol);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    for (shared_ptr<Index> index : node->getIndices()) {
        newNode->getIndices().push_back(dynamic_pointer_cast<Index>(wrappedVisit(index)));
    }

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<QualifiedIdentifier> node) {
    shared_ptr<SimpleIdentifier> newId = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->getIdentifier()));
    shared_ptr<Sort> newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->getSort()));

    shared_ptr<QualifiedIdentifier> newNode = make_shared<QualifiedIdentifier>(newId, newSort);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<DecimalLiteral> node) {
    shared_ptr<DecimalLiteral> newNode = make_shared<DecimalLiteral>(node->getValue());

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<NumeralLiteral> node) {
    shared_ptr<NumeralLiteral> newNode = make_shared<NumeralLiteral>(node->getValue(), node->getBase());

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<StringLiteral> node) {
    shared_ptr<StringLiteral> newNode = make_shared<StringLiteral>(node->getValue());

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<Logic> node) {
    shared_ptr<Symbol> newName = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getName()));

    shared_ptr<Logic> newNode = make_shared<Logic>(newName);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    for (shared_ptr<Attribute> attr : node->getAttributes()) {
        newNode->getAttributes().push_back(dynamic_pointer_cast<Attribute>(wrappedVisit(attr)));
    }

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<Theory> node) {
    shared_ptr<Symbol> newName = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getName()));

    shared_ptr<Theory> newNode = make_shared<Theory>(newName);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    for (shared_ptr<Attribute> attr : node->getAttributes()) {
        newNode->getAttributes().push_back(dynamic_pointer_cast<Attribute>(wrappedVisit(attr)));
    }

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<Script> node) {
    vector<shared_ptr<Command>> newCommands;
    for (shared_ptr<Command> cmd : node->getCommands()) {
        newCommands.push_back(dynamic_pointer_cast<Command>(wrappedVisit(cmd)));
    }

    shared_ptr<Script> newNode = make_shared<Script>(newCommands);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<Sort> node) {
    shared_ptr<SimpleIdentifier> newId = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->getIdentifier()));

    shared_ptr<Sort> newNode = make_shared<Sort>(newId);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    for (shared_ptr<Sort> arg : node->getArgs()) {
        shared_ptr<Sort> newArg = dynamic_pointer_cast<Sort>(wrappedVisit(arg));
        newNode->getArgs().push_back(newArg);
    }

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<CompSExpression> node) {
    vector<shared_ptr<SExpression>> newExps;
    for (shared_ptr<SExpression> exp : node->getExpressions()) {
        newExps.push_back(dynamic_pointer_cast<SExpression>(wrappedVisit(exp)));
    }

    shared_ptr<CompSExpression> newNode = make_shared<CompSExpression>(newExps);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SortSymbolDeclaration> node) {
    shared_ptr<SimpleIdentifier> newId = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->getIdentifier()));
    shared_ptr<NumeralLiteral> newArity = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->getArity()));

    shared_ptr<SortSymbolDeclaration> newNode = make_shared<SortSymbolDeclaration>(newId, newArity);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    for (shared_ptr<Attribute> attr : node->getAttributes()) {
        shared_ptr<Attribute> newArg = dynamic_pointer_cast<Attribute>(wrappedVisit(attr));
        newNode->getAttributes().push_back(newArg);
    }

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SortDeclaration> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));
    shared_ptr<NumeralLiteral> newArity = dynamic_pointer_cast<NumeralLiteral>(wrappedVisit(node->getArity()));

    shared_ptr<SortDeclaration> newNode = make_shared<SortDeclaration>(newSymbol, newArity);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SelectorDeclaration> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));
    shared_ptr<Sort> newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->getSort()));

    shared_ptr<SelectorDeclaration> newNode = make_shared<SelectorDeclaration>(newSymbol, newSort);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<ConstructorDeclaration> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));

    vector<shared_ptr<SelectorDeclaration>> newSelectors;
    for (shared_ptr<SelectorDeclaration> selectr : node->getSelectors()) {
        newSelectors.push_back(dynamic_pointer_cast<SelectorDeclaration>(wrappedVisit(selectr)));
    }

    shared_ptr<ConstructorDeclaration> newNode = make_shared<ConstructorDeclaration>(newSymbol, newSelectors);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SimpleDatatypeDeclaration> node) {
    vector<shared_ptr<ConstructorDeclaration>> newConstructors;
    for (shared_ptr<ConstructorDeclaration> constr : node->getConstructors()) {
        newConstructors.push_back(dynamic_pointer_cast<ConstructorDeclaration>(wrappedVisit(constr)));
    }

    shared_ptr<SimpleDatatypeDeclaration> newNode = make_shared<SimpleDatatypeDeclaration>(newConstructors);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<ParametricDatatypeDeclaration> node) {
    vector<shared_ptr<Symbol>> newParams;
    for (shared_ptr<Symbol> param : node->getParams()) {
        newParams.push_back(dynamic_pointer_cast<Symbol>(wrappedVisit(param)));
    }

    vector<shared_ptr<ConstructorDeclaration>> newConstructors;
    for (shared_ptr<ConstructorDeclaration> constr : node->getConstructors()) {
        newConstructors.push_back(dynamic_pointer_cast<ConstructorDeclaration>(wrappedVisit(constr)));
    }

    shared_ptr<ParametricDatatypeDeclaration> newNode = make_shared<ParametricDatatypeDeclaration>(newParams, newConstructors);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<QualifiedConstructor> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));
    shared_ptr<Sort> newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->getSort()));

    shared_ptr<QualifiedConstructor> newNode = make_shared<QualifiedConstructor>(newSymbol, newSort);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<QualifiedPattern> node) {
    vector<shared_ptr<Symbol>> newSymbols;
    for (shared_ptr<Symbol> symbol : node->getSymbols()) {
        newSymbols.push_back(dynamic_pointer_cast<Symbol>(wrappedVisit(symbol)));
    }

    shared_ptr<Constructor> newCons = dynamic_pointer_cast<Constructor>(wrappedVisit(node->getConstructor()));

    shared_ptr<QualifiedPattern> newNode = make_shared<QualifiedPattern>(newCons, newSymbols);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<MatchCase> node) {
    shared_ptr<Pattern> newPattern = dynamic_pointer_cast<Pattern>(wrappedVisit(node->getPattern()));
    shared_ptr<Term> newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->getTerm()));

    shared_ptr<MatchCase> newNode = make_shared<MatchCase>(newPattern, newTerm);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SpecConstFunDeclaration> node) {
    shared_ptr<SpecConstant> newConstant = dynamic_pointer_cast<SpecConstant>(wrappedVisit(node->getConstant()));
    shared_ptr<Sort> newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->getSort()));

    shared_ptr<SpecConstFunDeclaration> newNode = make_shared<SpecConstFunDeclaration>(newConstant, newSort);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    for (shared_ptr<Attribute> attr : node->getAttributes()) {
        shared_ptr<Attribute> newArg = dynamic_pointer_cast<Attribute>(wrappedVisit(attr));
        newNode->getAttributes().push_back(newArg);
    }

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<MetaSpecConstFunDeclaration> node) {
    shared_ptr<MetaSpecConstant> newConstant = dynamic_pointer_cast<MetaSpecConstant>(wrappedVisit(node->getConstant()));
    shared_ptr<Sort> newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->getSort()));

    shared_ptr<MetaSpecConstFunDeclaration> newNode = make_shared<MetaSpecConstFunDeclaration>(newConstant, newSort);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    for (shared_ptr<Attribute> attr : node->getAttributes()) {
        shared_ptr<Attribute> newArg = dynamic_pointer_cast<Attribute>(wrappedVisit(attr));
        newNode->getAttributes().push_back(newArg);
    }

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SimpleFunDeclaration> node) {
    shared_ptr<SimpleIdentifier> newIdentifier = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->getIdentifier()));

    vector<shared_ptr<Sort>> newSignature;
    for (shared_ptr<Sort> sort : node->getSignature()) {
        newSignature.push_back(dynamic_pointer_cast<Sort>(wrappedVisit(sort)));
    }

    shared_ptr<SimpleFunDeclaration> newNode = make_shared<SimpleFunDeclaration>(newIdentifier, newSignature);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    for (shared_ptr<Attribute> attr : node->getAttributes()) {
        shared_ptr<Attribute> newArg = dynamic_pointer_cast<Attribute>(wrappedVisit(attr));
        newNode->getAttributes().push_back(newArg);
    }

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<ParametricFunDeclaration> node) {
    vector<shared_ptr<Symbol>> newParams;
    for (shared_ptr<Symbol> param : node->getParams()) {
        newParams.push_back(dynamic_pointer_cast<Symbol>(wrappedVisit(param)));
    }

    shared_ptr<SimpleIdentifier> newIdentifier = dynamic_pointer_cast<SimpleIdentifier>(wrappedVisit(node->getIdentifier()));

    vector<shared_ptr<Sort>> newSignature;
    for (shared_ptr<Sort> sort : node->getSignature()) {
        newSignature.push_back(dynamic_pointer_cast<Sort>(wrappedVisit(sort)));
    }

    shared_ptr<ParametricFunDeclaration> newNode = make_shared<ParametricFunDeclaration>(newParams, newIdentifier, newSignature);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    for (shared_ptr<Attribute> attr : node->getAttributes()) {
        shared_ptr<Attribute> newArg = dynamic_pointer_cast<Attribute>(wrappedVisit(attr));
        newNode->getAttributes().push_back(newArg);
    }

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<QualifiedTerm> node) {
    shared_ptr<Identifier> newId = dynamic_pointer_cast<Identifier>(wrappedVisit(node->getIdentifier()));

    vector<shared_ptr<Term>> newTerms;
    for (shared_ptr<Term> term : node->getTerms()) {
        newTerms.push_back(dynamic_pointer_cast<Term>(wrappedVisit(term)));
    }

    shared_ptr<QualifiedTerm> newNode = make_shared<QualifiedTerm>(newId, newTerms);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<LetTerm> node) {
    vector<shared_ptr<VarBinding>> newBindings;
    for (shared_ptr<VarBinding> binding : node->getBindings()) {
        newBindings.push_back(dynamic_pointer_cast<VarBinding>(wrappedVisit(binding)));
    }

    shared_ptr<Term> newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->getTerm()));

    shared_ptr<LetTerm> newNode = make_shared<LetTerm>(newBindings, newTerm);
    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<ForallTerm> node) {
    vector<shared_ptr<SortedVariable>> newBindings;
    for (shared_ptr<SortedVariable> binding : node->getBindings()) {
        newBindings.push_back(dynamic_pointer_cast<SortedVariable>(wrappedVisit(binding)));
    }

    shared_ptr<Term> newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->getTerm()));

    shared_ptr<ForallTerm> newNode = make_shared<ForallTerm>(newBindings, newTerm);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<ExistsTerm> node) {
    vector<shared_ptr<SortedVariable>> newBindings;
    for (shared_ptr<SortedVariable> binding : node->getBindings()) {
        newBindings.push_back(dynamic_pointer_cast<SortedVariable>(wrappedVisit(binding)));
    }

    shared_ptr<Term> newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->getTerm()));

    shared_ptr<ExistsTerm> newNode = make_shared<ExistsTerm>(newBindings, newTerm);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}



void NodeDuplicator::visit(shared_ptr<MatchTerm> node) {
    shared_ptr<Term> newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->getTerm()));

    vector<shared_ptr<MatchCase>> newCases;
    for (shared_ptr<MatchCase> mcase : node->getCases()) {
        newCases.push_back(dynamic_pointer_cast<MatchCase>(wrappedVisit(mcase)));
    }

    shared_ptr<MatchTerm> newNode = make_shared<MatchTerm>(newTerm, newCases);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<AnnotatedTerm> node) {
    shared_ptr<Term> newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->getTerm()));

    vector<shared_ptr<Attribute>> newAttrs;
    for (shared_ptr<Attribute> attr : node->getAttributes()) {
        newAttrs.push_back(dynamic_pointer_cast<Attribute>(wrappedVisit(attr)));
    }

    shared_ptr<AnnotatedTerm> newNode = make_shared<AnnotatedTerm>(newTerm, newAttrs);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<SortedVariable> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));
    shared_ptr<Sort> newSort = dynamic_pointer_cast<Sort>(wrappedVisit(node->getSort()));

    shared_ptr<SortedVariable> newNode = make_shared<SortedVariable>(newSymbol, newSort);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}

void NodeDuplicator::visit(shared_ptr<VarBinding> node) {
    shared_ptr<Symbol> newSymbol = dynamic_pointer_cast<Symbol>(wrappedVisit(node->getSymbol()));
    shared_ptr<Term> newTerm = dynamic_pointer_cast<Term>(wrappedVisit(node->getTerm()));

    shared_ptr<VarBinding> newNode = make_shared<VarBinding>(newSymbol, newTerm);

    newNode->setColLeft(node->getColLeft());
    newNode->setColRight(node->getColRight());
    newNode->setRowLeft(node->getRowLeft());
    newNode->setRowRight(node->getRowRight());
 	newNode->setFilename(node->getFilename());

    ret = newNode;
}



