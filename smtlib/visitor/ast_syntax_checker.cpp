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
#include "../util/error_messages.h"

#include <iostream>
#include <memory>
#include <regex>
#include <vector>

using namespace std;
using namespace smtlib;
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
    for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
        if (name == (*paramIt)->toString())
            isParam = true;
    }

    if (isParam) {
        paramUsage[name] = true;

        if (!sort->getArgs().empty()) {
            err = addError(ErrorMessages::buildSortParamArity(sort->toString(), name), source, err);
        }
    } else {
        vector<shared_ptr<Sort>> argSorts = sort->getArgs();
        for (auto argIt = argSorts.begin(); argIt != argSorts.end(); argIt++) {
            checkParamUsage(params, paramUsage, *argIt, source, err);
        }
    }

    return err;
}

void SyntaxChecker::visit(shared_ptr<Attribute> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getKeyword()) {
        err = addError(ErrorMessages::ERR_ATTR_MISSING_KEYWORD, node, err);
    } else {
        visit0(node->getKeyword());
    }

    visit0(node->getValue());
}

void SyntaxChecker::visit(shared_ptr<CompAttributeValue> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->getValues());
}

void SyntaxChecker::visit(shared_ptr<Symbol> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!regex_match(node->getValue(), regexSymbol)) {
        err = addError(ErrorMessages::ERR_SYMBOL_MALFORMED, node, err);
    }
}

void SyntaxChecker::visit(shared_ptr<Keyword> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!regex_match(node->getValue(), regexKeyword)) {
        err = addError(ErrorMessages::ERR_KEYWORD_MALFORMED, node, err);
    }
}

void SyntaxChecker::visit(shared_ptr<MetaSpecConstant> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<BooleanValue> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<PropLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_PROP_LIT_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->getSymbol());
    }
}

void SyntaxChecker::visit(shared_ptr<AssertCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getTerm()) {
        err = addError(ErrorMessages::ERR_ASSERT_MISSING_TERM, node, err);
    } else {
        visit0(node->getTerm());
    }
}

void SyntaxChecker::visit(shared_ptr<CheckSatCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<CheckSatAssumCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->getAssumptions());
}

void SyntaxChecker::visit(shared_ptr<DeclareConstCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_DECL_CONST_MISSING_NAME, node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getSort()) {
        err = addError(ErrorMessages::ERR_DECL_CONST_MISSING_SORT, node, err);
    } else {
        visit0(node->getSort());
    }
}


void SyntaxChecker::visit(shared_ptr<DeclareDatatypeCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPE_MISSING_NAME, node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getDeclaration()) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPE_MISSING_DECL, node, err);
    } else {
        visit0(node->getDeclaration());
    }
}

void SyntaxChecker::visit(shared_ptr<DeclareDatatypesCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->getSorts().empty()) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPES_MISSING_SORTS, node, err);
    }

    if (node->getDeclarations().empty()) {
        err = addError(ErrorMessages::ERR_DECL_DATATYPES_MISSING_DECLS, node, err);
    }

    unsigned long sortCount = node->getSorts().size();
    unsigned long declCount = node->getDeclarations().size();

    if (node->getSorts().size() != node->getDeclarations().size()) {
        err = addError(ErrorMessages::buildDeclDatatypesCount(sortCount, declCount), node, err);
    }

    unsigned long minCount = sortCount < declCount ? sortCount : declCount;
    for (unsigned long i = 0; i < minCount; i++) {
        unsigned long arity = (unsigned long)node->getSorts()[i]->getArity()->getValue();
        unsigned long paramCount = 0;
        shared_ptr<ParametricDatatypeDeclaration> decl =
                dynamic_pointer_cast<ParametricDatatypeDeclaration>(node->getDeclarations()[i]);
        if (decl) {
            paramCount = decl->getParams().size();
        }

        if (arity != paramCount) {
            err = addError(ErrorMessages::buildDeclDatatypeArity(
                    node->getSorts()[i]->getSymbol()->toString(), arity, paramCount), node, err);
        }
    }

    visit0(node->getSorts());

    visit0(node->getDeclarations());
}

void SyntaxChecker::visit(shared_ptr<DeclareFunCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_DECL_FUN_MISSING_NAME, node, err);
    } else {
        visit0(node->getSymbol());
    }

    visit0(node->getParams());

    if (!node->getSort()) {
        err = addError(ErrorMessages::ERR_DECL_FUN_MISSING_RET, node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<DeclareSortCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_DECL_SORT_MISSING_NAME, node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getArity()) {
        err = addError(ErrorMessages::ERR_DECL_SORT_MISSING_ARITY, node, err);
    } else {
        visit0(node->getArity());
    }
}

void SyntaxChecker::visit(shared_ptr<DefineFunCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getDefinition()) {
        err = addError(ErrorMessages::ERR_DEF_FUN_MISSING_DEF, node, err);
    } else {
        visit0(node->getDefinition());
    }
}

void SyntaxChecker::visit(shared_ptr<DefineFunRecCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getDefinition()) {
        err = addError(ErrorMessages::ERR_DEF_FUN_REC_MISSING_DEF, node, err);
    } else {
        visit0(node->getDefinition());
    }
}

void SyntaxChecker::visit(shared_ptr<DefineFunsRecCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->getDeclarations().empty()) {
        err = addError(ErrorMessages::ERR_DEF_FUNS_REC_EMPTY_DECLS, node, err);
    }

    if (node->getBodies().empty()) {
        err = addError(ErrorMessages::ERR_DEF_FUNS_REC_EMPTY_BODIES, node, err);
    }

    unsigned long declCount = node->getDeclarations().size();
    unsigned long bodyCount = node->getBodies().size();


    if (declCount != bodyCount) {
        err = addError(ErrorMessages::buildDefFunsRecCount(declCount, bodyCount), node, err);
    }

    visit0(node->getDeclarations());

    visit0(node->getDeclarations());
}

void SyntaxChecker::visit(shared_ptr<DefineSortCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    // Check symbol
    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_DEF_SORT_MISSING_NAME, node, err);
    } else {
        visit0(node->getSymbol());
    }

    // Check parameter list
    visit0(node->getParams());

    // Check definition
    if (!node->getSort()) {
        err = addError(ErrorMessages::ERR_DEF_SORT_MISSING_DEF, node, err);
    } else {
        visit0(node->getSort());
    }

    // Check parameter usage
    unordered_map<string, bool> paramUsage;
    err = checkParamUsage(node->getParams(), paramUsage, node->getSort(), node, err);

    if (paramUsage.size() != node->getParams().size()) {
        vector<string> unusedParams;
        vector<shared_ptr<Symbol>> params = node->getParams();
        for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
            string pname = (*paramIt)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                unusedParams.push_back("'" + pname + "'");
            }
        }
        err = addError(ErrorMessages::buildSortDefUnusedSortParams(unusedParams), node, err);
    }
}

void SyntaxChecker::visit(shared_ptr<EchoCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->getMessage() == "") {
        err = addError(ErrorMessages::ERR_ECHO_EMPTY_STRING, node, err);
    }

}

void SyntaxChecker::visit(shared_ptr<ExitCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetAssertsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetAssignsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetInfoCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getFlag()) {
        err = addError(ErrorMessages::ERR_GET_INFO_MISSING_FLAG, node, err);
    } else {
        visit0(node->getFlag());
    }
}

void SyntaxChecker::visit(shared_ptr<GetModelCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetOptionCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getOption()) {
        err = addError(ErrorMessages::ERR_GET_OPT_MISSING_OPT, node, err);
    } else {
        visit0(node->getOption());
    }
}

void SyntaxChecker::visit(shared_ptr<GetProofCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetUnsatAssumsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetUnsatCoreCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<GetValueCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->getTerms().empty()) {
        err = addError(ErrorMessages::ERR_GET_VALUE_EMPTY_TERMS, node, err);
    } else {
        visit0(node->getTerms());
    }
}

void SyntaxChecker::visit(shared_ptr<PopCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getNumeral()) {
        err = addError(ErrorMessages::ERR_POP_MISSING_NUMERAL, node, err);
    } else {
        visit0(node->getNumeral());
    }
}

void SyntaxChecker::visit(shared_ptr<PushCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getNumeral()) {
        err = addError(ErrorMessages::ERR_PUSH_MISSING_NUMERAL, node, err);
    } else {
        visit0(node->getNumeral());
    }
}

void SyntaxChecker::visit(shared_ptr<ResetCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<ResetAssertsCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<SetInfoCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getInfo()) {
        err = addError(ErrorMessages::ERR_SET_INFO_MISSING_INFO, node, err);
    } else {
        visit0(node->getInfo());
    }
}

void SyntaxChecker::visit(shared_ptr<SetLogicCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getLogic()) {
        err = addError(ErrorMessages::ERR_SET_LOGIC_MISSING_LOGIC, node, err);
    }
}

void SyntaxChecker::visit(shared_ptr<SetOptionCommand> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getOption()) {
        err = addError(ErrorMessages::ERR_SET_OPT_MISSING_OPT, node, err);
    } else {
        shared_ptr<Attribute> option = node->getOption();
        if ((option->getKeyword()->getValue() == KW_DIAG_OUTPUT_CHANNEL
             || option->getKeyword()->getValue() == KW_REGULAR_OUTPUT_CHANNEL)
            && !dynamic_cast<StringLiteral *>(option->getValue().get())) {
            err = addError(ErrorMessages::ERR_OPT_VALUE_STRING, option, err);
        } else if ((option->getKeyword()->getValue() == KW_RANDOM_SEED
                    || option->getKeyword()->getValue() == KW_VERBOSITY
                    || option->getKeyword()->getValue() == KW_REPROD_RESOURCE_LIMIT)
                   && !dynamic_cast<NumeralLiteral *>(option->getValue().get())) {
            err = addError(ErrorMessages::ERR_OPT_VALUE_NUMERAL, option, err);
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
                err = addError(ErrorMessages::ERR_OPT_VALUE_BOOLEAN, option, err);
            }
        }

        visit0(node->getOption());
    }
}

void SyntaxChecker::visit(shared_ptr<FunctionDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_FUN_DECL_MISSING_NAME, node, err);
    } else {
        visit0(node->getSymbol());
    }

    visit0(node->getParams());

    if (!node->getSort()) {
        err = addError(ErrorMessages::ERR_FUN_DECL_MISSING_RET, node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<FunctionDefinition> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSignature()) {
        err = addError(ErrorMessages::ERR_FUN_DEF_MISSING_SIG, node, err);
    } else {
        visit0(node->getSignature());
    }

    if (!node->getBody()) {
        err = addError(ErrorMessages::ERR_FUN_DEF_MISSING_BODY, node, err);
    } else {
        visit0(node->getBody());
    }
}

void SyntaxChecker::visit(shared_ptr<SimpleIdentifier> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_ID_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (node->isIndexed() && node->getIndices().empty()) {
        err = addError(ErrorMessages::ERR_ID_EMPTY_INDICES, node, err);
    }

    visit0(node->getIndices());
}

void SyntaxChecker::visit(shared_ptr<QualifiedIdentifier> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getIdentifier()) {
        err = addError(ErrorMessages::ERR_QUAL_ID_MISSING_ID, node, err);
    } else {
        visit0(node->getIdentifier());
    }

    if (!node->getSort()) {
        err = addError(ErrorMessages::ERR_QUAL_ID_MISSING_SORT, node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<DecimalLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<NumeralLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<StringLiteral> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }
}

void SyntaxChecker::visit(shared_ptr<Logic> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if (!node->getName()) {
        err = addError(ErrorMessages::ERR_LOGIC_MISSING_NAME, node, err);
    }

    if (attrs.empty()) {
        err = addError(ErrorMessages::ERR_LOGIC_EMPTY_ATTRS, node, err);
    }

    for (auto attrIt = attrs.begin(); attrIt != attrs.end(); attrIt++) {
        shared_ptr<Attribute> attr = *attrIt;
        if (!attr)
            continue;

        shared_ptr<SyntaxCheckError> attrerr;

        if (attr->getKeyword()->getValue() == KW_LANGUAGE
            || attr->getKeyword()->getValue() == KW_EXTENSIONS
            || attr->getKeyword()->getValue() == KW_VALUES
            || attr->getKeyword()->getValue() == KW_NOTES) {
            if (!dynamic_cast<StringLiteral *>(attr->getValue().get())) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_STRING, attr, attrerr);
            }
        } else if (attr->getKeyword()->getValue() == KW_THEORIES) {
            if (!dynamic_cast<CompAttributeValue *>(attr->getValue().get())) {
                err = addError(ErrorMessages::ERR_ATTR_VALUE_THEORIES, attr, err);
            } else {
                CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
                vector<shared_ptr<AttributeValue>> values = val->getValues();

                // Note: standard prohibits empty theory list, but there are logics that only use Core
                /*if (values.empty()) {
                    err = addError(ErrorMessages::ERR_ATTR_VALUE_THEORIES_EMPTY, attr, err);
                }*/

                for (auto valueIt = values.begin(); valueIt != values.begin(); valueIt++) {
                    if ((*valueIt) && !dynamic_cast<Symbol *>((*valueIt).get())) {
                        attrerr = addError(ErrorMessages::buildAttrValueSymbol((*valueIt)->toString()), attr, attrerr);
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
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if (!node->getName()) {
        err = addError(ErrorMessages::ERR_THEORY_MISSING_NAME, node, err);
    }

    if (attrs.empty()) {
        err = addError(ErrorMessages::ERR_THEORY_EMPTY_ATTRS, node, err);
    }

    for (auto attrIt = attrs.begin(); attrIt != attrs.end(); attrIt++) {
        shared_ptr<Attribute> attr = *attrIt;
        if (!attr)
            continue;

        shared_ptr<SyntaxCheckError> attrerr;

        if (attr->getKeyword()->getValue() == KW_SORTS_DESC
            || attr->getKeyword()->getValue() == KW_FUNS_DESC
            || attr->getKeyword()->getValue() == KW_DEFINITION
            || attr->getKeyword()->getValue() == KW_VALUES
            || attr->getKeyword()->getValue() == KW_NOTES) {
            if (!dynamic_cast<StringLiteral *>(attr->getValue().get())) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_STRING, attr, attrerr);
            }
        } else if (attr->getKeyword()->getValue() == KW_SORTS) {
            if (!dynamic_cast<CompAttributeValue *>(attr->getValue().get())) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_SORTS, attr, attrerr);
            } else {
                CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
                vector<shared_ptr<AttributeValue>> values = val->getValues();

                if (values.empty()) {
                    attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_SORTS_EMPTY, attr, attrerr);
                }

                for (auto valueIt = values.begin(); valueIt != values.begin(); valueIt++) {
                    if ((*valueIt) && !dynamic_cast<SortSymbolDeclaration *>((*valueIt).get())) {
                        attrerr = addError(
                                ErrorMessages::buildAttrValueSortDecl((*valueIt)->toString()), attr, attrerr);
                    }
                }
            }
        } else if (attr->getKeyword()->getValue() == KW_FUNS) {
            if (!dynamic_cast<CompAttributeValue *>(attr->getValue().get())) {
                attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_FUNS, attr, attrerr);
            } else {
                CompAttributeValue *val = dynamic_cast<CompAttributeValue *>(attr->getValue().get());
                vector<shared_ptr<AttributeValue>> values = val->getValues();

                if (values.empty()) {
                    attrerr = addError(ErrorMessages::ERR_ATTR_VALUE_FUNS_EMPTY, attr, attrerr);
                }

                for (auto valueIt = values.begin(); valueIt != values.begin(); valueIt++) {
                    if ((*valueIt) && !dynamic_cast<FunSymbolDeclaration *>((*valueIt).get())) {
                        attrerr = addError(
                                ErrorMessages::buildAttrValueFunDecl((*valueIt)->toString()), attr, attrerr);
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
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->getCommands());
}

void SyntaxChecker::visit(shared_ptr<Sort> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getIdentifier()) {
        err = addError(ErrorMessages::ERR_SORT_MISSING_ID, node, err);
    } else {
        visit0(node->getIdentifier());
    }

    if (node->hasArgs() && node->getArgs().empty()) {
        err = addError(ErrorMessages::ERR_SORT_EMPTY_ARGS, node, err);
    } else {
        visit0(node->getArgs());
    }
}

void SyntaxChecker::visit(shared_ptr<CompSExpression> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    visit0(node->getExpressions());
}

void SyntaxChecker::visit(shared_ptr<SortSymbolDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getIdentifier()) {
        err = addError(ErrorMessages::ERR_SORT_SYM_DECL_MISSING_ID, node, err);
    } else {
        visit0(node->getIdentifier());
    }

    if (!node->getArity()) {
        err = addError(ErrorMessages::ERR_SORT_SYM_DECL_MISSING_ARITY, node, err);
    } else {
        visit0(node->getArity());
    }

    visit0(node->getAttributes());
}

void SyntaxChecker::visit(shared_ptr<SpecConstFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getConstant()) {
        err = addError(ErrorMessages::ERR_SPEC_CONST_DECL_MISSING_CONST, node, err);
    } else {
        visit0(node->getConstant());
    }

    if (!node->getSort()) {
        err = addError(ErrorMessages::ERR_SPEC_CONST_DECL_MISSING_SORT, node, err);
    } else {
        visit0(node->getSort());
    }

    visit0(node->getAttributes());
}

void SyntaxChecker::visit(shared_ptr<MetaSpecConstFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getConstant()) {
        err = addError(ErrorMessages::ERR_META_SPEC_CONST_DECL_MISSING_CONST, node, err);
    } else {
        visit0(node->getConstant());
    }

    if (!node->getSort()) {
        err = addError(ErrorMessages::ERR_META_SPEC_CONST_DECL_MISSING_SORT, node, err);
    } else {
        visit0(node->getSort());
    }

    visit0(node->getAttributes());
}

void SyntaxChecker::visit(shared_ptr<SimpleFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getIdentifier()) {
        err = addError(ErrorMessages::ERR_FUN_SYM_DECL_MISSING_ID, node, err);
    } else {
        visit0(node->getIdentifier());
    }

    if (node->getSignature().empty()) {
        err = addError(ErrorMessages::ERR_FUN_SYM_DECL_EMPTY_SIG, node, err);
    } else {
        visit0(node->getSignature());
    }

    visit0(node->getAttributes());
}

void SyntaxChecker::visit(shared_ptr<ParametricFunDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    // Check parameter list
    if (node->getParams().empty()) {
        err = addError(ErrorMessages::ERR_PARAM_FUN_SYM_DECL_EMPTY_PARAMS, node, err);
    } else {
        visit0(node->getParams());
    }

    // Check identifier
    if (!node->getIdentifier()) {
        err = addError(ErrorMessages::ERR_PARAM_FUN_SYM_DECL_MISSING_ID, node, err);
    } else {
        visit0(node->getIdentifier());
    }

    // Check signature
    if (node->getSignature().empty()) {
        err = addError(ErrorMessages::ERR_PARAM_FUN_SYM_DECL_EMPTY_SIG, node, err);
    } else {
        visit0(node->getSignature());
    }

    // Check parameter usage
    unordered_map<string, bool> paramUsage;
    vector<shared_ptr<Sort>> sig = node->getSignature();
    for (auto sortIt = sig.begin(); sortIt != sig.end(); sortIt++) {
        err = checkParamUsage(node->getParams(), paramUsage, *sortIt, node, err);
    }

    if (paramUsage.size() != node->getParams().size()) {
        vector<string> unusedParams;
        vector<shared_ptr<Symbol>> params = node->getParams();
        for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
            string pname = (*paramIt)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                unusedParams.push_back("'" + pname + "'");
            }
        }

        err = addError(ErrorMessages::buildParamFunDeclUnusedSortParams(unusedParams), node, err);
    }

    // Check attribute list
    visit0(node->getAttributes());
}

void SyntaxChecker::visit(shared_ptr<SortDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_SORT_DECL_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getArity()) {
        err = addError(ErrorMessages::ERR_SORT_DECL_MISSING_ARITY, node, err);
    } else {
        visit0(node->getArity());
    }
}

void SyntaxChecker::visit(shared_ptr<SelectorDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_SEL_DECL_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getSort()) {
        err = addError(ErrorMessages::ERR_SEL_DECL_MISSING_SORT, node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<ConstructorDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_CONS_DECL_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->getSymbol());
    }

    vector<shared_ptr<SelectorDeclaration>> &selectors = node->getSelectors();
    for (auto selIt = selectors.begin(); selIt != selectors.end(); selIt++) {
        visit0((*selIt));
    }
}


void SyntaxChecker::visit(shared_ptr<SimpleDatatypeDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->getConstructors().empty()) {
        err = addError(ErrorMessages::ERR_DATATYPE_DECL_EMPTY_CONS, node, err);
    } else {
        visit0(node->getConstructors());
    }

}

void SyntaxChecker::visit(shared_ptr<ParametricDatatypeDeclaration> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->getParams().empty()) {
        err = addError(ErrorMessages::ERR_PARAM_DATATYPE_DECL_EMPTY_PARAMS, node, err);
    } else {
        visit0(node->getParams());
    }

    if (node->getConstructors().empty()) {
        err = addError(ErrorMessages::ERR_PARAM_DATATYPE_DECL_EMPTY_CONS, node, err);
    } else {
        visit0(node->getConstructors());
    }

    std::unordered_map<std::string, bool> paramUsage;

    vector<shared_ptr<ConstructorDeclaration>> constructors = node->getConstructors();
    for (auto consIt = constructors.begin(); consIt != constructors.end(); consIt++) {
        vector<shared_ptr<SelectorDeclaration>> selectors = (*consIt)->getSelectors();
        for (auto selit = selectors.begin(); selit != selectors.end(); selit++) {
            err = checkParamUsage(node->getParams(), paramUsage, (*selit)->getSort(), node, err);
        }
    }

    if (paramUsage.size() != node->getParams().size()) {
        vector<string> unusedParams;
        vector<shared_ptr<Symbol>> params = node->getParams();
        for (auto paramIt = params.begin(); paramIt != params.end(); paramIt++) {
            string pname = (*paramIt)->toString();
            if (paramUsage.find(pname) == paramUsage.end()) {
                unusedParams.push_back("'" + pname + "'");
            }
        }
        err = addError(ErrorMessages::buildParamDatatypeDeclUnusedSortParams(unusedParams), node, err);
    }
}

void SyntaxChecker::visit(shared_ptr<QualifiedConstructor> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_QUAL_CONS_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getSort()) {
        err = addError(ErrorMessages::ERR_QUAL_CONS_MISSING_SORT, node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<QualifiedPattern> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getConstructor()) {
        err = addError(ErrorMessages::ERR_QUAL_PATTERN_MISSING_CONS, node, err);
    } else {
        visit0(node->getConstructor());
    }

    if (node->getSymbols().empty()) {
        err = addError(ErrorMessages::ERR_QUAL_PATTERN_EMPTY_SYMS, node, err);
    } else {
        visit0(node->getSymbols());
    }
}

void SyntaxChecker::visit(shared_ptr<MatchCase> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getPattern()) {
        err = addError(ErrorMessages::ERR_MATCH_CASE_MISSING_PATTERN, node, err);
    } else {
        visit0(node->getPattern());
    }

    if (!node->getTerm()) {
        err = addError(ErrorMessages::ERR_MATCH_CASE_MISSING_TERM, node, err);
    } else {
        visit0(node->getTerm());
    }
}

void SyntaxChecker::visit(shared_ptr<QualifiedTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getIdentifier()) {
        err = addError(ErrorMessages::ERR_QUAL_TERM_MISSING_ID, node, err);
    } else {
        visit0(node->getIdentifier());
    }

    if (node->getTerms().empty()) {
        err = addError(ErrorMessages::ERR_QUAL_TERM_EMPTY_TERMS, node, err);
    } else {
        visit0(node->getTerms());
    }
}

void SyntaxChecker::visit(shared_ptr<LetTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->getBindings().empty()) {
        err = addError(ErrorMessages::ERR_LET_TERM_EMPTY_VARS, node, err);
    } else {
        vector<shared_ptr<VarBinding>> &bindings = node->getBindings();
        for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
            visit0((*bindingIt));
        }
    }

    if (!node->getTerm()) {
        err = addError(ErrorMessages::ERR_LET_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->getTerm());
    }
}

void SyntaxChecker::visit(shared_ptr<ForallTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->getBindings().empty()) {
        err = addError(ErrorMessages::ERR_FORALL_TERM_EMPTY_VARS, node, err);
    } else {
        vector<shared_ptr<SortedVariable>> &bindings = node->getBindings();
        for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
            visit0((*bindingIt));
        }
    }

    if (!node->getTerm()) {
        err = addError(ErrorMessages::ERR_FORALL_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->getTerm());
    }
}

void SyntaxChecker::visit(shared_ptr<ExistsTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (node->getBindings().empty()) {
        err = addError(ErrorMessages::ERR_EXISTS_TERM_EMPTY_VARS, node, err);
    } else {
        vector<shared_ptr<SortedVariable>> &bindings = node->getBindings();
        for (auto bindingIt = bindings.begin(); bindingIt != bindings.end(); bindingIt++) {
            visit0((*bindingIt));
        }
    }

    if (!node->getTerm()) {
        err = addError(ErrorMessages::ERR_EXISTS_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->getTerm());
    }
}

void SyntaxChecker::visit(shared_ptr<MatchTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getTerm()) {
        err = addError(ErrorMessages::ERR_MATCH_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->getTerm());
    }

    if (node->getCases().empty()) {
        err = addError(ErrorMessages::ERR_MATCH_TERM_EMPTY_CASES, node, err);
    } else {
        vector<shared_ptr<MatchCase>> &cases = node->getCases();
        for (auto caseIt = cases.begin(); caseIt != cases.end(); caseIt++) {
            visit0((*caseIt));
        }
    }
}

void SyntaxChecker::visit(shared_ptr<AnnotatedTerm> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getTerm()) {
        err = addError(ErrorMessages::ERR_ANNOT_TERM_MISSING_TERM, node, err);
    } else {
        visit0(node->getTerm());
    }

    if (node->getAttributes().empty()) {
        err = addError(ErrorMessages::ERR_ANNOT_TERM_EMPTY_ATTRS, node, err);
    } else {
        visit0(node->getAttributes());
    }
}

void SyntaxChecker::visit(shared_ptr<SortedVariable> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_SORTED_VAR_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getSort()) {
        err = addError(ErrorMessages::ERR_SORTED_VAR_MISSING_SORT, node, err);
    } else {
        visit0(node->getSort());
    }
}

void SyntaxChecker::visit(shared_ptr<VarBinding> node) {
    shared_ptr<SyntaxCheckError> err;

    if (!node) {
        err = addError(ErrorMessages::ERR_NULL_NODE_VISIT, node, err);
        return;
    }

    if (!node->getSymbol()) {
        err = addError(ErrorMessages::ERR_VAR_BIND_MISSING_SYMBOL, node, err);
    } else {
        visit0(node->getSymbol());
    }

    if (!node->getTerm()) {
        err = addError(ErrorMessages::ERR_VAR_BIND_MISSING_SORT, node, err);
    } else {
        visit0(node->getTerm());
    }
}

string SyntaxChecker::getErrors() {
    stringstream ss;
    for (auto errIt = errors.begin(); errIt != errors.end(); errIt++) {
        shared_ptr<SyntaxCheckError> err = *errIt;
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
        for (auto itt = err->messages.begin(); itt != err->messages.end(); itt++) {
            ss << "\t" << *itt << "." << endl;
        }

        ss << endl;
    }

    return ss.str();
}