#include "ast_syntax_checker.h"
#include "../ast/ast_attribute.h"
#include "../ast/ast_command.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_sexp.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_term.h"
#include "../ast/ast_theory.h"

#include <iostream>
#include <memory>
#include <regex>
#include <vector>

using namespace std;
using namespace smtlib::ast;

shared_ptr<SyntaxChecker::SyntaxCheckError> SyntaxChecker::addError(string message, std::shared_ptr<AstNode> node,
                                                                    shared_ptr<SyntaxChecker::SyntaxCheckError> err) {
    if (!err) {
        err = make_shared<SyntaxCheckError>();
        err->messages.push_back(message);
        err->node = node;
        errors.push_back(err);
    } else {
        err->messages.push_back(message);
    }

    return err;
}

void SyntaxChecker::visit(std::shared_ptr<Attribute> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getKeyword()) {
        ret = false;
        err = addError("Missing keyword from attribute", node, err);
    } else {
        node->getKeyword()->accept(this);
    }

    if (node->getValue())
        node->getValue()->accept(this);
}

void SyntaxChecker::visit(std::shared_ptr<CompAttributeValue> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    std::vector<std::shared_ptr<AttributeValue>> &vals = node->getValues();
    for (std::vector<std::shared_ptr<AttributeValue>>::iterator it = vals.begin(); it != vals.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<Symbol> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!std::regex_match(node->getValue(), regexSymbol)) {
        ret = false;
        err = addError("Malformed symbol", node, err);
    }
}

void SyntaxChecker::visit(std::shared_ptr<Keyword> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<MetaSpecConstant> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<BooleanValue> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<PropLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        ret = false;
        err = addError("Missing symbol from propositional literal", node, err);
    } else {
        node->getSymbol()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<AssertCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getTerm()) {
        ret = false;
        err = addError("Missing term from assert command", node, err);
    } else {
        node->getTerm()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<CheckSatCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<CheckSatAssumCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    std::vector<std::shared_ptr<PropLiteral>> &assums = node->getAssumptions();
    for (std::vector<std::shared_ptr<PropLiteral>>::iterator it = assums.begin(); it != assums.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<DeclareConstCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        ret = false;
        err = addError("Missing constant name from declare-const command", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    if (!node->getSort()) {
        ret = false;
        err = addError("Missing constant sort from declare-const command", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<DeclareFunCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        ret = false;
        err = addError("Missing function name from declare-fun command", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    std::vector<std::shared_ptr<Sort>> &params = node->getParams();
    for (std::vector<std::shared_ptr<Sort>>::iterator it = params.begin(); it != params.end(); it++) {
        (*it)->accept(this);
    }

    if (!node->getSort()) {
        ret = false;
        err = addError("Missing function sort from declare-fun command", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<DeclareSortCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        ret = false;
        err = addError("Missing sort name from declare-sort command", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    if (!node->getArity()) {
        ret = false;
        err = addError("Missing sort arity from declare-sort command", node, err);
    } else {
        node->getArity()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<DefineFunCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getDefinition()) {
        ret = false;
        err = addError("Missing function definition from define-fun command", node, err);
    } else {
        node->getDefinition()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<DefineFunRecCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getDefinition()) {
        ret = false;
        err = addError("Missing function definition from define-fun-rec command", node, err);
    } else {
        node->getDefinition()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<DefineFunsRecCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getDeclarations().empty()) {
        ret = false;
        err = addError("Missing function declarations from define-funs-rec command", node, err);
    }

    if (node->getBodies().empty()) {
        ret = false;
        err = addError("Missing function bodies from define-funs-rec command", node, err);
    }

    if (node->getBodies().size() != node->getDeclarations().size()) {
        ret = false;
        err = addError(
                "Number of function declarations is not equal to the number of function bodies in define-funs-rec command",
                node, err);
    }

    std::vector<std::shared_ptr<FunctionDeclaration>> &decls = node->getDeclarations();
    for (std::vector<std::shared_ptr<FunctionDeclaration>>::iterator it = decls.begin();
         it != decls.end(); it++) {
        (*it)->accept(this);
    }

    std::vector<std::shared_ptr<FunctionDeclaration>> &bodies = node->getDeclarations();
    for (std::vector<std::shared_ptr<FunctionDeclaration>>::iterator it = bodies.begin();
         it != bodies.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<DefineSortCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        ret = false;
        err = addError("Missing sort name from define-sort command", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    std::vector<std::shared_ptr<Symbol>> &params = node->getParams();
    for (std::vector<std::shared_ptr<Symbol>>::iterator it = params.begin(); it != params.end(); it++) {
        (*it)->accept(this);
    }

    if (!node->getSort()) {
        ret = false;
        err = addError("Missing sort from define-sort command", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<EchoCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getMessage() == "") {
        err = addError("Attempting to echo empty string", node, err);
        ret = false;
    }

}

void SyntaxChecker::visit(std::shared_ptr<ExitCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<GetAssertsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<GetAssignsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<GetInfoCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getFlag()) {
        ret = false;
        err = addError("Missing flag in get-info command", node, err);
    } else {
        node->getFlag()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<GetModelCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<GetOptionCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getOption()) {
        ret = false;
        err = addError("Missing option in get-option command", node, err);
    } else {
        node->getOption()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<GetProofCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<GetUnsatAssumsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<GetUnsatCoreCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<GetValueCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getTerms().empty()) {
        ret = false;
        err = addError("Missing terms in get-value command", node, err);
    } else {
        std::vector<std::shared_ptr<Term>> &terms = node->getTerms();
        for (std::vector<std::shared_ptr<Term>>::iterator it = terms.begin(); it != terms.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(std::shared_ptr<PopCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getNumeral()) {
        ret = false;
        err = addError("Missing numeral in pop command", node, err);
    } else {
        node->getNumeral()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<PushCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getNumeral()) {
        ret = false;
        err = addError("Missing numeral in push command", node, err);
    } else {
        node->getNumeral()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<ResetCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<ResetAssertsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<SetInfoCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getInfo()) {
        ret = false;
        err = addError("Missing info in set-info command", node, err);
    } else {
        node->getInfo()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<SetLogicCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getLogic()) {
        ret = false;
        err = addError("Missing logic in set-logic command", node, err);
    }
}

void SyntaxChecker::visit(std::shared_ptr<SetOptionCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getOption()) {
        ret = false;
        err = addError("Missing option in set-option command", node, err);
    } else {
        shared_ptr<Attribute> option = node->getOption();
        if ((option->getKeyword()->getValue() == ":diagnostic-output-channel"
             || option->getKeyword()->getValue() == ":regular-output-channel")
            && !dynamic_cast<StringLiteral const*>(option->getValue().get())) {
            ret = false;
            err = addError("Option value should be string literal", option, err);
        } else if ((option->getKeyword()->getValue() == ":random-seed"
                    || option->getKeyword()->getValue() == ":verbosity"
                    || option->getKeyword()->getValue() == ":reproducible-resource-limit")
                   && !dynamic_cast<NumeralLiteral const*>(option->getValue().get())) {
            ret = false;
            err = addError("Option value should be numeral literal", option, err);
        } else if ((option->getKeyword()->getValue() == ":expand-definitions"
                    || option->getKeyword()->getValue() == ":global-declarations"
                    || option->getKeyword()->getValue() == ":interactive-mode"
                    || option->getKeyword()->getValue() == ":print-success"
                    || option->getKeyword()->getValue() == ":produce-assertions"
                    || option->getKeyword()->getValue() == ":produce-assignments"
                    || option->getKeyword()->getValue() == ":produce-models"
                    || option->getKeyword()->getValue() == ":produce-proofs"
                    || option->getKeyword()->getValue() == ":produce-unsat-assumptions"
                    || option->getKeyword()->getValue() == ":produce-unsat-cores")
                   && !dynamic_cast<BooleanValue const*>(option->getValue().get())) {
            ret = false;
            err = addError("Option value should be boolean", option, err);
        }

        node->getOption()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<FunctionDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        ret = false;
        err = addError("Missing name from function declaration", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    std::vector<std::shared_ptr<SortedVariable>> &params = node->getParams();
    for (std::vector<std::shared_ptr<SortedVariable>>::iterator it = params.begin(); it != params.end(); it++) {
        (*it)->accept(this);
    }

    if (!node->getSort()) {
        ret = false;
        err = addError("Missing return sort from function declaration", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<FunctionDefinition> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSignature()) {
        ret = false;
        err = addError("Missing signature from function definition", node, err);
    } else {
        node->getSignature()->accept(this);
    }

    if (!node->getBody()) {
        ret = false;
        err = addError("Missing body from function definition", node, err);
    } else {
        node->getBody()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<SimpleIdentifier> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        ret = false;
        err = addError("Missing symbol from identifier", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    if (node->isIndexed() && node->getIndices().empty()) {
        ret = false;
        err = addError("Indexed identifier has no indices", node, err);
    }

    std::vector<std::shared_ptr<Index>> &indices = node->getIndices();
    for (std::vector<std::shared_ptr<Index>>::iterator it = indices.begin(); it != indices.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<QualifiedIdentifier> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from qualified identifier", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if (!node->getSort()) {
        ret = false;
        err = addError("Missing sort from qualified identifier", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<DecimalLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<NumeralLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<StringLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(std::shared_ptr<Logic> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        ret = false;
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if (!node->getName()) {
        ret = false;
        err = addError("Missing logic name", node, err);
    }

    if (attrs.empty()) {
        ret = false;
        err = addError("Logic has no attributes", node, err);
    }

    for (vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;
        if (attr->getKeyword()->getValue() == ":language"
            || attr->getKeyword()->getValue() == ":extensions"
            || attr->getKeyword()->getValue() == ":values"
            || attr->getKeyword()->getValue() == ":notes") {

            if (!dynamic_cast<StringLiteral const*>(attr->getValue().get())) {
                ret = false;
                err = addError("Attribute value should be string literal", attr, err);
            }
        } else if (attr->getKeyword()->getValue() == ":theories") {
            if (!dynamic_cast<CompAttributeValue const*>(attr->getValue().get())) {
                ret = false;
                err = addError("Attribute value should be a list of theory names", attr, err);
            } else {
                CompAttributeValue* val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
                vector<shared_ptr<AttributeValue>> values = val->getValues();

                /*if (values.empty()) {
                    ret = false;
                    err = addError("Empty list of theory names", attr, err);
                }*/

                for (vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                    if (!dynamic_cast<Symbol const*>((*itt).get())) {
                        ret = false;
                        err = addError("Attribute value should be a symbol", (*itt), err);
                    }
                }
            }
        }

        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<Theory> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if (!node->getName()) {
        ret = false;
        err = addError("Missing theory name", node, err);
    }

    if (attrs.empty()) {
        ret = false;
        err = addError("Theory has no attributes", node, err);
    }

    for (vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;
        if (attr->getKeyword()->getValue() == ":sorts-description"
            || attr->getKeyword()->getValue() == ":funs-description"
            || attr->getKeyword()->getValue() == ":definition"
            || attr->getKeyword()->getValue() == ":values"
            || attr->getKeyword()->getValue() == ":notes") {
            if(dynamic_cast<StringLiteral const*>(attr->getValue().get())) {
                ret = false;
                err = addError("Attribute value should be string literal", attr, err);
            }
        } else if (attr->getKeyword()->getValue() == ":sorts") {
            if(!dynamic_cast<CompAttributeValue const*>(attr->getValue().get())) {
                ret = false;
                err = addError("Attribute value should be a list of sort symbol declarations", attr, err);
            } else {
                CompAttributeValue* val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
                vector<shared_ptr<AttributeValue>> values = val->getValues();

                if (values.empty()) {
                    ret = false;
                    err = addError("Empty list of sort symbol declarations", attr, err);
                }

                for (vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                    if (!dynamic_cast<SortSymbolDeclaration const*>((*itt).get())) {
                        ret = false;
                        err = addError("Attribute value should be a sort symbol declaration", (*itt), err);
                    }
                }
            }
        } else if (attr->getKeyword()->getValue() == ":funs") {
            if(!dynamic_cast<CompAttributeValue const*>(attr->getValue().get())) {
                ret = false;
                err = addError("Attribute value should be a list of function symbol declarations", attr, err);
            } else {
                CompAttributeValue* val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
                vector<shared_ptr<AttributeValue>> values = val->getValues();

                if (values.empty()) {
                    ret = false;
                    err = addError("Empty list of function symbol declarations", attr, err);
                }

                for (vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                    if (!dynamic_cast<FunSymbolDeclaration*>((*itt).get())) {
                        ret = false;
                        err = addError("Attribute value should be a function symbol declaration", (*itt), err);
                    }
                }
            }
        }

        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<Script> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    std::vector<std::shared_ptr<Command>> &commands = node->getCommands();
    for (std::vector<std::shared_ptr<Command>>::iterator it = commands.begin(); it != commands.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<Sort> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from sort", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if (node->hasArgs() && node->getArgs().empty()) {
        ret = false;
        err = addError("Parametrized sort has no parameters", node, err);
    } else {
        std::vector<std::shared_ptr<Sort>> &params = node->getArgs();
        for (std::vector<std::shared_ptr<Sort>>::iterator it = params.begin(); it != params.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(std::shared_ptr<CompSExpression> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    std::vector<std::shared_ptr<SExpression>> &exprs = node->getExpressions();
    for (std::vector<std::shared_ptr<SExpression>>::iterator it = exprs.begin(); it != exprs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<SortSymbolDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from sort symbol declaration", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if (!node->getArity()) {
        ret = false;
        err = addError("Missing arity from sort symbol declaration", node, err);
    } else {
        node->getArity()->accept(this);
    }

    std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for (std::vector<std::shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<SpecConstFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getConstant()) {
        ret = false;
        err = addError("Missing constant from spec constant function symbol declaration", node, err);
    } else {
        node->getConstant()->accept(this);
    }

    if (!node->getSort()) {
        ret = false;
        err = addError("Missing sort from spec constant function symbol declaration", node, err);
    } else {
        node->getSort()->accept(this);
    }

    std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for (std::vector<std::shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<MetaSpecConstFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getConstant()) {
        ret = false;
        err = addError("Missing constant from meta spec constant function symbol declaration", node, err);
    } else {
        node->getConstant()->accept(this);
    }

    if (!node->getSort()) {
        ret = false;
        err = addError("Missing sort from meta spec constant function symbol declaration", node, err);
    } else {
        node->getSort()->accept(this);
    }

    std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for (std::vector<std::shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<SimpleFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from function symbol declaration", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if (node->getSignature().empty()) {
        ret = false;
        err = addError("Empty signature for function symbol declaration", node, err);
    } else {
        std::vector<std::shared_ptr<Sort>> &sig = node->getSignature();
        for (std::vector<std::shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
            (*it)->accept(this);
        }
    }

    std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for (std::vector<std::shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<ParametricFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from parametric function symbol declaration", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if (node->getSignature().empty()) {
        ret = false;
        err = addError("Empty signature for parametric function symbol declaration", node, err);
    } else {
        std::vector<std::shared_ptr<Sort>> &sig = node->getSignature();
        for (std::vector<std::shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
            (*it)->accept(this);
        }
    }

    if (node->getParams().empty()) {
        ret = false;
        err = addError("Empty parameter list for parametric function symbol declaration", node, err);
    } else {
        std::vector<std::shared_ptr<Symbol>> &params = node->getParams();
        for (std::vector<std::shared_ptr<Symbol>>::iterator it = params.begin(); it != params.end(); it++) {
            (*it)->accept(this);
        }
    }

    std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for (std::vector<std::shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<QualifiedTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from qualified term", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if (node->getTerms().empty()) {
        ret = false;
        err = addError("Empty term list for qualified term", node, err);
    } else {
        std::vector<std::shared_ptr<Term>> &terms = node->getTerms();
        for (std::vector<std::shared_ptr<Term>>::iterator it = terms.begin(); it != terms.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(std::shared_ptr<LetTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getTerm()) {
        ret = false;
        err = addError("Missing term from let term", node, err);
    } else {
        node->getTerm()->accept(this);
    }

    if (node->getBindings().empty()) {
        ret = false;
        err = addError("Empty variable binding list for let term", node, err);
    } else {
        std::vector<std::shared_ptr<VarBinding>> &bindings = node->getBindings();
        for (std::vector<std::shared_ptr<VarBinding>>::iterator it = bindings.begin();
             it != bindings.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(std::shared_ptr<ForallTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getTerm()) {
        ret = false;
        err = addError("Missing term from forall term", node, err);
    } else {
        node->getTerm()->accept(this);
    }

    if (node->getBindings().empty()) {
        ret = false;
        err = addError("Empty variable binding list for forall term", node, err);
    } else {
        std::vector<std::shared_ptr<SortedVariable>> &bindings = node->getBindings();
        for (std::vector<std::shared_ptr<SortedVariable>>::iterator it = bindings.begin();
             it != bindings.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(std::shared_ptr<ExistsTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getTerm()) {
        ret = false;
        err = addError("Missing term from exists term", node, err);
    } else {
        node->getTerm()->accept(this);
    }

    if (node->getBindings().empty()) {
        ret = false;
        err = addError("Empty variable binding list for exists term", node, err);
    } else {
        std::vector<std::shared_ptr<SortedVariable>> &bindings = node->getBindings();
        for (std::vector<std::shared_ptr<SortedVariable>>::iterator it = bindings.begin();
             it != bindings.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(std::shared_ptr<AnnotatedTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getTerm()) {
        ret = false;
        err = addError("Missing term from annotated term", node, err);
    } else {
        node->getTerm()->accept(this);
    }

    if (node->getAttributes().empty()) {
        ret = false;
        err = addError("Empty attribute list for exists term", node, err);
    } else {
        std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
        for (std::vector<std::shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(std::shared_ptr<SortedVariable> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        ret = false;
        err = addError("Missing symbol from sorted variable", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    if (!node->getSort()) {
        ret = false;
        err = addError("Missing sort from sorted variable", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(std::shared_ptr<VarBinding> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        ret = false;
        err = addError("Missing symbol from variable binding", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    if (!node->getTerm()) {
        ret = false;
        err = addError("Missing sort from variable binding", node, err);
    } else {
        node->getTerm()->accept(this);
    }
}

string SyntaxChecker::getErrors() {
    stringstream ss;
    for (vector<shared_ptr<SyntaxCheckError>>::iterator it = errors.begin(); it != errors.end(); it++) {
        shared_ptr<SyntaxCheckError> err = *it;
        if (err->node) {
            ss << err->node->getRowLeft() << ":" << err->node->getColLeft()
            << " - " << err->node->getRowRight() << ":" << err->node->getColRight() << "   ";

            string nodestr = err->node->toString();
            if (nodestr.length() > 100)
                ss << string(nodestr, 100) << "[...]";
            else
                ss << nodestr;
        } else {
            ss << "NULL";
        }

        ss << endl;
        for (std::vector<std::string>::iterator itt = err->messages.begin(); itt != err->messages.end(); itt++) {
            ss << "\t" << *itt << "." << endl;
        }

        ss << endl;
    }

    return ss.str();
}