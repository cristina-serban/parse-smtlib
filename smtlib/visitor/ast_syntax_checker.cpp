#include "ast_syntax_checker.h"
#include "../ast/ast_attribute.h"
#include "../ast/ast_command.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_sexp.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_term.h"
#include "../ast/ast_theory.h"
#include "../util/global_settings.h"

#include <iostream>
#include <memory>
#include <regex>
#include <vector>

using namespace std;
using namespace smtlib::ast;

shared_ptr<SyntaxChecker::SyntaxCheckError>
SyntaxChecker::addError(string message, shared_ptr<AstNode> node,
                        shared_ptr<SyntaxChecker::SyntaxCheckError> err) {
    if (!err) {
        err = make_shared<SyntaxCheckError>(message, node);
        errors.push_back(err);
    } else {
        err->messages.push_back(message);
    }

    return err;
}

shared_ptr<SyntaxChecker::SyntaxCheckError>
SyntaxChecker::checkParamUsage(vector<shared_ptr<Symbol>> &params,
                               unordered_map<string, bool> &paramUsage,
                               shared_ptr<Sort> sort,
                               shared_ptr<AstNode> source,
                               shared_ptr<SyntaxCheckError> err) {
    if (!sort)
        return err;

    string name = sort->getIdentifier()->toString();
    bool isParam = false;
    for (vector<shared_ptr<Symbol>>::iterator it = params.begin(); it != params.end(); it++) {
        if (name == (*it)->toString())
            isParam = true;
    }

    if (isParam) {
        paramUsage[name] = true;

        if (!sort->getArgs().empty()) {
            err = addError(sort->toString() + ": '" + name +
                           "' is a sort parameter - it should have an arity of 0 ", source, err);
        }
    } else {
        for (vector<shared_ptr<Sort>>::iterator it = sort->getArgs().begin();
             it != sort->getArgs().end(); it++) {
            checkParamUsage(params, paramUsage, *it, source, err);
        }
    }

    return err;
}

void SyntaxChecker::visit(shared_ptr<Attribute> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getKeyword()) {
        err = addError("Missing keyword from attribute", node, err);
    } else {
        visit0(node->getKeyword());
    }

    visit0(node->getValue());
}

void SyntaxChecker::visit(shared_ptr<CompAttributeValue> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    visit0(node->getValues());
}

void SyntaxChecker::visit(shared_ptr<Symbol> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!regex_match(node->getValue(), regexSymbol)) {
        err = addError("Malformed symbol", node, err);
    }
}

void SyntaxChecker::visit(shared_ptr<Keyword> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!regex_match(node->getValue(), regexKeyword)) {
        err = addError("Malformed keyword", node, err);
    }
}

void SyntaxChecker::visit(shared_ptr<MetaSpecConstant> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<BooleanValue> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<PropLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing symbol from propositional literal", node, err);
    } else {
        visit0(node->getSymbol());
    }
}

void SyntaxChecker::visit(shared_ptr<AssertCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getTerm()) {
        err = addError("Missing term from assert command", node, err);
    } else {
        visit0(node->getTerm());
    }
}

void SyntaxChecker::visit(shared_ptr<CheckSatCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<CheckSatAssumCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    visit0(node->getAssumptions());
}

void SyntaxChecker::visit(shared_ptr<DeclareConstCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing constant name from declare-const command", node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getSort()) {
        err = addError("Missing constant sort from declare-const command", node, err);
    } else {
        visit0(node->getSort());
    }
}


void SyntaxChecker::visit(shared_ptr<DeclareDatatypeCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing datatype name from declare-datatype command", node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getDeclaration()) {
        err = addError("Missing datatype declaration from declare-datatype command", node, err);
    } else {
        visit0(node->getDeclaration());
    }
}

void SyntaxChecker::visit(shared_ptr<DeclareDatatypesCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getSorts().empty()) {
        err = addError("Missing sort declarations from declare-datatypes command", node, err);
    }

    if (node->getDeclarations().empty()) {
        err = addError("Missing datatype declarations from declare-datatypes command", node, err);
    }

    unsigned long sortCount = node->getSorts().size();
    unsigned long declCount = node->getDeclarations().size();

    if (node->getSorts().size() != node->getDeclarations().size()) {
        stringstream ss;
        ss << "Number of sort declarations (" << sortCount
        << ") is not equal to the number of datatype declarations ("
        << declCount << ") in declare-datatypes command";
        err = addError(ss.str(), node, err);
    }

    unsigned long minCount = sortCount < declCount ? sortCount : declCount;
    for (unsigned long i = 0; i < minCount; i++) {
        long arity = node->getSorts()[i]->getArity()->getValue();
        long params = 0;
        shared_ptr<ParametricDatatypeDeclaration> decl =
                dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->getDeclarations()[i]);
        if (decl) {
            params = decl->getParams().size();
        }

        if (arity != params) {
            stringstream ss;
            ss << "Datatype '" << node->getSorts()[i]->getSymbol()->toString() << "' has an arity of " << arity
            << " but its declaration has " << params << " parameter" << (params == 1 ? "" : "s");
            err = addError(ss.str(), node, err);
        }
    }

    visit0(node->getSorts());

    visit0(node->getDeclarations());
}

void SyntaxChecker::visit(shared_ptr<DeclareFunCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing function name from declare-fun command", node, err);
    } else {
        visit0(node->getSymbol());
    }

    visit0(node->getParams());

    if (!node->getSort()) {
        err = addError("Missing function sort from declare-fun command", node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<DeclareSortCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing sort name from declare-sort command", node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getArity()) {
        err = addError("Missing sort arity from declare-sort command", node, err);
    } else {
        visit0(node->getArity());
    }
}

void SyntaxChecker::visit(shared_ptr<DefineFunCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getDefinition()) {
        err = addError("Missing function definition from define-fun command", node, err);
    } else {
        visit0(node->getDefinition());
    }
}

void SyntaxChecker::visit(shared_ptr<DefineFunRecCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getDefinition()) {
        err = addError("Missing function definition from define-fun-rec command", node, err);
    } else {
        visit0(node->getDefinition());
    }
}

void SyntaxChecker::visit(shared_ptr<DefineFunsRecCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getDeclarations().empty()) {
        err = addError("Missing function declarations from define-funs-rec command", node, err);
    }

    if (node->getBodies().empty()) {
        err = addError("Missing function bodies from define-funs-rec command", node, err);
    }

    unsigned long declCount = node->getDeclarations().size();
    unsigned long bodyCount = node->getBodies().size();


    if (declCount != bodyCount) {
        stringstream ss;
        ss << "Number of function declarations (" << declCount
        << ") is not equal to the number of function bodies ("
        << bodyCount << ") in define-funs-rec command";
        err = addError(ss.str(), node, err);
    }

    visit0(node->getDeclarations());

    visit0(node->getDeclarations());
}

void SyntaxChecker::visit(shared_ptr<DefineSortCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    // Check symbol
    if (!node->getSymbol()) {
        err = addError("Missing sort name from define-sort command", node, err);
    } else {
        visit0(node->getSymbol());
    }

    // Check parameter list
    visit0(node->getParams());

    // Check definition
    if (!node->getSort()) {
        err = addError("Missing sort definition from define-sort command", node, err);
    } else {
        visit0(node->getSort());
    }

    // Check parameter usage
    unordered_map<string, bool> paramUsage;
    err = checkParamUsage(node->getParams(), paramUsage, node->getSort(), node, err);

    if (paramUsage.size() != node->getParams().size()) {
        long diff = node->getParams().size() - paramUsage.size();

        stringstream ss;
        ss << "Sort parameter" << ((diff == 1) ? " " : "s ");
        bool first = true;
        for (vector<shared_ptr<Symbol>>::iterator it = node->getParams().begin();
             it != node->getParams().end(); it++) {
            string pname = (*it)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                if (!first) {
                    ss << ", ";
                } else {
                    first = false;
                }
                ss << "'" << pname << "'";
            }
        }
        ss << ((diff == 1) ? " is " : " are ") << "not used in sort definition";
        err = addError(ss.str(), node, err);
    }
}

void SyntaxChecker::visit(shared_ptr<EchoCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getMessage() == "") {
        err = addError("Attempting to echo empty string", node, err);
    }

}

void SyntaxChecker::visit(shared_ptr<ExitCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetAssertsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetAssignsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetInfoCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getFlag()) {
        err = addError("Missing flag in get-info command", node, err);
    } else {
        visit0(node->getFlag());
    }
}

void SyntaxChecker::visit(shared_ptr<GetModelCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetOptionCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getOption()) {
        err = addError("Missing option in get-option command", node, err);
    } else {
        visit0(node->getOption());
    }
}

void SyntaxChecker::visit(shared_ptr<GetProofCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetUnsatAssumsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetUnsatCoreCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetValueCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getTerms().empty()) {
        err = addError("Missing terms in get-value command", node, err);
    } else {
        visit0(node->getTerms());
    }
}

void SyntaxChecker::visit(shared_ptr<PopCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getNumeral()) {
        err = addError("Missing numeral in pop command", node, err);
    } else {
        visit0(node->getNumeral());
    }
}

void SyntaxChecker::visit(shared_ptr<PushCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getNumeral()) {
        err = addError("Missing numeral in push command", node, err);
    } else {
        visit0(node->getNumeral());
    }
}

void SyntaxChecker::visit(shared_ptr<ResetCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<ResetAssertsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<SetInfoCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getInfo()) {
        err = addError("Missing info in set-info command", node, err);
    } else {
        visit0(node->getInfo());
    }
}

void SyntaxChecker::visit(shared_ptr<SetLogicCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getLogic()) {
        err = addError("Missing logic in set-logic command", node, err);
    }
}

void SyntaxChecker::visit(shared_ptr<SetOptionCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getOption()) {
        err = addError("Missing option in set-option command", node, err);
    } else {
        shared_ptr<Attribute> option = node->getOption();
        if ((option->getKeyword()->getValue() == KW_DIAG_OUTPUT_CHANNEL
             || option->getKeyword()->getValue() == KW_REGULAR_OUTPUT_CHANNEL)
            && !dynamic_cast<StringLiteral *>(option->getValue().get())) {
            err = addError("Option value should be string literal", option, err);
        } else if ((option->getKeyword()->getValue() == KW_RANDOM_SEED
                    || option->getKeyword()->getValue() == KW_VERBOSITY
                    || option->getKeyword()->getValue() == KW_REPROD_RESOURCE_LIMIT)
                   && !dynamic_cast<NumeralLiteral *>(option->getValue().get())) {
            err = addError("Option value should be numeral literal", option, err);
        } else if ((option->getKeyword()->getValue() == KW_EXPAND_DEFS
                    || option->getKeyword()->getValue() == KW_GLOBAL_DECLS
                    || option->getKeyword()->getValue() == KW_INTERACTIVE_MODE
                    || option->getKeyword()->getValue() == KW_PRINT_SUCCESS
                    || option->getKeyword()->getValue() == KW_PROD_ASSERTS
                    || option->getKeyword()->getValue() == KW_PROD_ASSIGNS
                    || option->getKeyword()->getValue() == KW_PROD_MODELS
                    || option->getKeyword()->getValue() == KW_PROD_PROOFS
                    || option->getKeyword()->getValue() == KW_PROD_UNSAT_ASSUMS
                    || option->getKeyword()->getValue() == KW_PROD_UNSAT_CORES)) {
            if (!option->getValue() || (option->getValue()->toString() != CONST_TRUE
                                        && option->getValue()->toString() != CONST_FALSE)) {
                err = addError("Option value should be boolean", option, err);
            }
        }

        visit0(node->getOption());
    }
}

void SyntaxChecker::visit(shared_ptr<FunctionDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing name from function declaration", node, err);
    } else {
        visit0(node->getSymbol());
    }

    visit0(node->getParams());

    if (!node->getSort()) {
        err = addError("Missing return sort from function declaration", node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<FunctionDefinition> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSignature()) {
        err = addError("Missing signature from function definition", node, err);
    } else {
        visit0(node->getSignature());
    }

    if (!node->getBody()) {
        err = addError("Missing body from function definition", node, err);
    } else {
        visit0(node->getBody());
    }
}

void SyntaxChecker::visit(shared_ptr<SimpleIdentifier> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing symbol from identifier", node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (node->isIndexed() && node->getIndices().empty()) {
        err = addError("Indexed identifier has no indices", node, err);
    }

    visit0(node->getIndices());
}

void SyntaxChecker::visit(shared_ptr<QualifiedIdentifier> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        err = addError("Missing identifier from qualified identifier", node, err);
    } else {
        visit0(node->getIdentifier());
    }

    if (!node->getSort()) {
        err = addError("Missing sort from qualified identifier", node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<DecimalLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<NumeralLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<StringLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<Logic> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if (!node->getName()) {
        err = addError("Missing logic name", node, err);
    }

    if (attrs.empty()) {
        err = addError("Logic has no attributes", node, err);
    }

    for (vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;
        if (!attr)
            continue;

        shared_ptr<SyntaxCheckError> attrerr;

        if (attr->getKeyword()->getValue() == KW_LANGUAGE
            || attr->getKeyword()->getValue() == KW_EXTENSIONS
            || attr->getKeyword()->getValue() == KW_VALUES
            || attr->getKeyword()->getValue() == KW_NOTES) {
            if (!dynamic_cast<StringLiteral *>(attr->getValue().get())) {
                attrerr = addError("Attribute value should be string literal", attr, attrerr);
            }
        } else if (attr->getKeyword()->getValue() == KW_THEORIES) {
            if (!dynamic_cast<CompAttributeValue *>(attr->getValue().get())) {
                err = addError("Attribute value should be a list of theory names", attr, err);
            } else {
                CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
                vector<shared_ptr<AttributeValue>> values = val->getValues();

                // Note: standard prohibits empty theory list, but there are logics that only use Core
                /*if (values.empty()) {
                    err = addError("Empty list of theory names", attr, err);
                }*/

                for (vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                    if ((*itt) && !dynamic_cast<Symbol *>((*itt).get())) {
                        attrerr = addError("Attribute value '" + (*itt)->toString()
                                           + "' should be a symbol", attr, attrerr);
                    }
                }
            }
        }

        visit0(attr);
    }
}

void SyntaxChecker::visit(shared_ptr<Theory> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if (!node->getName()) {
        err = addError("Missing theory name", node, err);
    }

    if (attrs.empty()) {
        err = addError("Theory has no attributes", node, err);
    }

    for (vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;
        if (!attr)
            continue;

        shared_ptr<SyntaxCheckError> attrerr;

        if (attr->getKeyword()->getValue() == KW_SORTS_DESC
            || attr->getKeyword()->getValue() == KW_FUNS_DESC
            || attr->getKeyword()->getValue() == KW_DEFINITION
            || attr->getKeyword()->getValue() == KW_VALUES
            || attr->getKeyword()->getValue() == KW_NOTES) {
            if (!dynamic_cast<StringLiteral *>(attr->getValue().get())) {
                attrerr = addError("Attribute value should be string literal", attr, attrerr);
            }
        } else if (attr->getKeyword()->getValue() == KW_SORTS) {
            if (!dynamic_cast<CompAttributeValue *>(attr->getValue().get())) {
                attrerr = addError("Attribute value should be a list of sort symbol declarations", attr, attrerr);
            } else {
                CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
                vector<shared_ptr<AttributeValue>> values = val->getValues();

                if (values.empty()) {
                    attrerr = addError("Empty list of sort symbol declarations", attr, attrerr);
                }

                for (vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                    if ((*itt) && !dynamic_cast<SortSymbolDeclaration *>((*itt).get())) {
                        attrerr = addError("Attribute value '" + (*itt)->toString()
                                           + "' should be a sort symbol declaration", attr, attrerr);
                    }
                }
            }
        } else if (attr->getKeyword()->getValue() == KW_FUNS) {
            if (!dynamic_cast<CompAttributeValue *>(attr->getValue().get())) {
                attrerr = addError("Attribute value should be a list of function symbol declarations", attr, attrerr);
            } else {
                CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
                vector<shared_ptr<AttributeValue>> values = val->getValues();

                if (values.empty()) {
                    attrerr = addError("Empty list of function symbol declarations", attr, attrerr);
                }

                for (vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                    if ((*itt) && !dynamic_cast<FunSymbolDeclaration *>((*itt).get())) {
                        attrerr = addError(
                                "Attribute value '" + (*itt)->toString() + "' should be a function symbol declaration",
                                (*itt), attrerr);
                    }
                }
            }
        }

        visit0(attr);
    }
}

void SyntaxChecker::visit(shared_ptr<Script> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    visit0(node->getCommands());
}

void SyntaxChecker::visit(shared_ptr<Sort> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        err = addError("Missing identifier from sort", node, err);
    } else {
        visit0(node->getIdentifier());
    }

    if (node->hasArgs() && node->getArgs().empty()) {
        err = addError("Parametric sort has no arguments", node, err);
    } else {
        visit0(node->getArgs());
    }
}

void SyntaxChecker::visit(shared_ptr<CompSExpression> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    visit0(node->getExpressions());
}

void SyntaxChecker::visit(shared_ptr<SortSymbolDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        err = addError("Missing identifier from sort symbol declaration", node, err);
    } else {
        visit0(node->getIdentifier());
    }

    if (!node->getArity()) {
        err = addError("Missing arity from sort symbol declaration", node, err);
    } else {
        visit0(node->getArity());
    }

    visit0(node->getAttributes());
}

void SyntaxChecker::visit(shared_ptr<SpecConstFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getConstant()) {
        err = addError("Missing constant from specification constant function symbol declaration", node, err);
    } else {
        visit0(node->getConstant());
    }

    if (!node->getSort()) {
        err = addError("Missing sort from specification function symbol declaration", node, err);
    } else {
        visit0(node->getSort());
    }

    visit0(node->getAttributes());
}

void SyntaxChecker::visit(shared_ptr<MetaSpecConstFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getConstant()) {
        err = addError("Missing constant from meta specification constant function symbol declaration", node, err);
    } else {
        visit0(node->getConstant());
    }

    if (!node->getSort()) {
        err = addError("Missing sort from meta specification constant function symbol declaration", node, err);
    } else {
        visit0(node->getSort());
    }

    visit0(node->getAttributes());
}

void SyntaxChecker::visit(shared_ptr<SimpleFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        err = addError("Missing identifier from function symbol declaration", node, err);
    } else {
        visit0(node->getIdentifier());
    }

    if (node->getSignature().empty()) {
        err = addError("Empty signature for function symbol declaration", node, err);
    } else {
        visit0(node->getSignature());
    }

    visit0(node->getAttributes());
}

void SyntaxChecker::visit(shared_ptr<ParametricFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    // Check parameter list
    if (node->getParams().empty()) {
        err = addError("Empty parameter list for parametric function symbol declaration", node, err);
    } else {
        visit0(node->getParams());
    }

    // Check identifier
    if (!node->getIdentifier()) {
        err = addError("Missing identifier from parametric function symbol declaration", node, err);
    } else {
        visit0(node->getIdentifier());
    }

    // Check signature
    if (node->getSignature().empty()) {
        err = addError("Empty signature for parametric function symbol declaration", node, err);
    } else {
        visit0(node->getSignature());
    }

    // Check parameter usage
    unordered_map<string, bool> paramUsage;
    vector<shared_ptr<Sort>> sig = node->getSignature();
    for (vector<shared_ptr<Sort>>::iterator it = sig.begin(); it != sig.end(); it++) {
        err = checkParamUsage(node->getParams(), paramUsage, *it, node, err);
    }

    if (paramUsage.size() != node->getParams().size()) {
        long diff = node->getParams().size() - paramUsage.size();

        stringstream ss;
        ss << "Sort parameter" << ((diff == 1) ? " " : "s ");
        bool first = true;
        for (vector<shared_ptr<Symbol>>::iterator it = node->getParams().begin();
             it != node->getParams().end(); it++) {
            string pname = (*it)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                if (!first) {
                    ss << ", ";
                } else {
                    first = false;
                }
                ss << "'" << pname << "'";
            }
        }
        ss << ((diff == 1) ? " is " : " are ") << "not used in parametric function declaration";
        err = addError(ss.str(), node, err);
    }

    // Check attribute list
    visit0(node->getAttributes());
}

void SyntaxChecker::visit(shared_ptr<SortDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing symbol from sort declaration", node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getArity()) {
        err = addError("Missing arity from sort declaration", node, err);
    } else {
        visit0(node->getArity());
    }
}

void SyntaxChecker::visit(shared_ptr<SelectorDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing symbol from selector declaration", node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getSort()) {
        err = addError("Missing sort from selector declaration", node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<ConstructorDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing symbol from constructor declaration", node, err);
    } else {
        visit0(node->getSymbol());
    }

    vector<shared_ptr<SelectorDeclaration>> &selectors = node->getSelectors();
    for (vector<shared_ptr<SelectorDeclaration>>::iterator it = selectors.begin();
         it != selectors.end(); it++) {
        visit0((*it));
    }
}


void SyntaxChecker::visit(shared_ptr<SimpleDatatypeDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getConstructors().empty()) {
        err = addError("Empty constructor list for datatype declaration", node, err);
    } else {
        visit0(node->getConstructors());
    }

}

void SyntaxChecker::visit(shared_ptr<ParametricDatatypeDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getParams().empty()) {
        err = addError("Empty parameter list for parametric datatype declaration", node, err);
    } else {
        visit0(node->getParams());
    }

    if (node->getConstructors().empty()) {
        err = addError("Empty constructor list for parametric datatype declaration", node, err);
    } else {
        visit0(node->getConstructors());
    }

    std::unordered_map<std::string, bool> paramUsage;

    for (vector<shared_ptr<ConstructorDeclaration>>::iterator consit = node->getConstructors().begin();
         consit != node->getConstructors().end(); consit++) {
        for (vector<shared_ptr<SelectorDeclaration>>::iterator selit = (*consit)->getSelectors().begin();
             selit != (*consit)->getSelectors().end(); selit++) {
            err = checkParamUsage(node->getParams(), paramUsage, (*selit)->getSort(), node, err);
        }
    }

    if (paramUsage.size() != node->getParams().size()) {
        long diff = node->getParams().size() - paramUsage.size();

        stringstream ss;
        ss << "Sort parameter" << ((diff == 1) ? " " : "s ");
        bool first = true;
        for (vector<shared_ptr<Symbol>>::iterator it = node->getParams().begin();
             it != node->getParams().end(); it++) {
            string pname = (*it)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                if (!first) {
                    ss << ", ";
                } else {
                    first = false;
                }
                ss << "'" << pname << "'";
            }
        }
        ss << ((diff == 1) ? " is " : " are ") << "not used in parametric datatype declaration";
        err = addError(ss.str(), node, err);
    }
}

void SyntaxChecker::visit(shared_ptr<QualifiedConstructor> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing symbol from qualified constructor", node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getSort()) {
        err = addError("Missing sort from qualified constructor", node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<QualifiedPattern> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getConstructor()) {
        err = addError("Missing constructor from qualified pattern", node, err);
    } else {
        visit0(node->getConstructor());
    }

    if (node->getSymbols().empty()) {
        err = addError("Empty symbol list for qualified pattern", node, err);
    } else {
        visit0(node->getSymbols());
    }
}

void SyntaxChecker::visit(shared_ptr<MatchCase> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getPattern()) {
        err = addError("Missing pattern from match case", node, err);
    } else {
        visit0(node->getPattern());
    }

    if (!node->getTerm()) {
        err = addError("Missing term from match case", node, err);
    } else {
        visit0(node->getTerm());
    }
}

void SyntaxChecker::visit(shared_ptr<QualifiedTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getIdentifier()) {
        err = addError("Missing identifier from qualified term", node, err);
    } else {
        visit0(node->getIdentifier());
    }

    if (node->getTerms().empty()) {
        err = addError("Empty term list for qualified term", node, err);
    } else {
        visit0(node->getTerms());
    }
}

void SyntaxChecker::visit(shared_ptr<LetTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getBindings().empty()) {
        err = addError("Empty variable binding list for let term", node, err);
    } else {
        vector<shared_ptr<VarBinding>> &bindings = node->getBindings();
        for (vector<shared_ptr<VarBinding>>::iterator it = bindings.begin();
             it != bindings.end(); it++) {
            visit0((*it));
        }
    }

    if (!node->getTerm()) {
        err = addError("Missing term from let term", node, err);
    } else {
        visit0(node->getTerm());
    }
}

void SyntaxChecker::visit(shared_ptr<ForallTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getBindings().empty()) {
        err = addError("Empty variable binding list for forall term", node, err);
    } else {
        vector<shared_ptr<SortedVariable>> &bindings = node->getBindings();
        for (vector<shared_ptr<SortedVariable>>::iterator it = bindings.begin();
             it != bindings.end(); it++) {
            visit0((*it));
        }
    }

    if (!node->getTerm()) {
        err = addError("Missing term from forall term", node, err);
    } else {
        visit0(node->getTerm());
    }
}

void SyntaxChecker::visit(shared_ptr<ExistsTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (node->getBindings().empty()) {
        err = addError("Empty variable binding list for exists term", node, err);
    } else {
        vector<shared_ptr<SortedVariable>> &bindings = node->getBindings();
        for (vector<shared_ptr<SortedVariable>>::iterator it = bindings.begin();
             it != bindings.end(); it++) {
            visit0((*it));
        }
    }

    if (!node->getTerm()) {
        err = addError("Missing term from exists term", node, err);
    } else {
        visit0(node->getTerm());
    }
}

void SyntaxChecker::visit(shared_ptr<MatchTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getTerm()) {
        err = addError("Missing term from match term", node, err);
    } else {
        visit0(node->getTerm());
    }

    if (node->getCases().empty()) {
        err = addError("Empty cases list for match term", node, err);
    } else {
        vector<shared_ptr<MatchCase>> &cases = node->getCases();
        for (vector<shared_ptr<MatchCase>>::iterator it = cases.begin();
             it != cases.end(); it++) {
            visit0((*it));
        }
    }
}

void SyntaxChecker::visit(shared_ptr<AnnotatedTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getTerm()) {
        err = addError("Missing term from annotated term", node, err);
    } else {
        visit0(node->getTerm());
    }

    if (node->getAttributes().empty()) {
        err = addError("Empty attribute list for annotated term", node, err);
    } else {
        visit0(node->getAttributes());
    }
}

void SyntaxChecker::visit(shared_ptr<SortedVariable> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing symbol from sorted variable", node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getSort()) {
        err = addError("Missing sort from sorted variable", node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<VarBinding> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError("Missing symbol from variable binding", node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getTerm()) {
        err = addError("Missing sort from variable binding", node, err);
    } else {
        visit0(node->getTerm());
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
                ss << string(nodestr, 0, 100) << "[...]";
            else
                ss << nodestr;
        } else {
            ss << "NULL";
        }

        ss << endl;
        for (vector<string>::iterator itt = err->messages.begin(); itt != err->messages.end(); itt++) {
            ss << "\t" << *itt << "." << endl;
        }

        ss << endl;
    }

    return ss.str();
}