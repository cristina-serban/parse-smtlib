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

shared_ptr<SyntaxChecker::SyntaxCheckError> SyntaxChecker::addError(string message, AstNode const *node,
                                                                    shared_ptr<SyntaxChecker::SyntaxCheckError> err) {
    if(!err) {
        err = make_shared<SyntaxCheckError>();
        err->messages.push_back(message);
        err->node = node;
        errors.push_back(err);
    } else {
        err->messages.push_back(message);
    }

    return err;
}

void SyntaxChecker::visit(Attribute const *node) {
    shared_ptr<SyntaxCheckError> err;

    if(!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if(!node->getKeyword()) {
        ret = false;
            err = addError("Missing keyword from attribute", node, err);
    } else {
        node->getKeyword()->accept(this);
    }

    if(node->getValue())
        node->getValue()->accept(this);
}

void SyntaxChecker::visit(CompoundAttributeValue const *node) {
	shared_ptr<SyntaxCheckError> err;

    if(!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    const std::vector<std::shared_ptr<AttributeValue>> &vals = node->getValues();
    for(std::vector<std::shared_ptr<AttributeValue>>::const_iterator it = vals.begin(); it != vals.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(Symbol const *node) {
	shared_ptr<SyntaxCheckError> err;

    if(!node) {
        err = addError("Attempt to visit NULL node", node, err);
        return;
    }

    if(!std::regex_match(node->getValue(), regexSymbol)) {
        ret = false;
        err = addError("Malformed symbol", node, err);
    }
}

void SyntaxChecker::visit(Keyword const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(MetaSpecConstant const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(BooleanValue const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(PropLiteral const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getSymbol()) {
        ret = false;
        err = addError("Missing symbol from propositional literal", node, err);
    } else {
        node->getSymbol()->accept(this);
    }
}

void SyntaxChecker::visit(AssertCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getTerm()) {
        ret = false;
        err = addError("Missing term from assert command", node, err);
    } else {
        node->getTerm()->accept(this);
    }
}

void SyntaxChecker::visit(CheckSatCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
}

void SyntaxChecker::visit(CheckSatAssumCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    const std::vector<std::shared_ptr<PropLiteral>> &assums = node->getAssumptions();
    for(std::vector<std::shared_ptr<PropLiteral>>::const_iterator it = assums.begin(); it != assums.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(DeclareConstCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getSymbol()) {
        ret = false;
        err = addError("Missing constant name from declare-const command", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        err = addError("Missing constant sort from declare-const command", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(DeclareFunCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getSymbol()) {
        ret = false;
        err = addError("Missing function name from declare-fun command", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    const std::vector<std::shared_ptr<Sort>> &params = node->getParams();
    for(std::vector<std::shared_ptr<Sort>>::const_iterator it = params.begin(); it != params.end(); it++) {
        (*it)->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        err = addError("Missing function sort from declare-fun command", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(DeclareSortCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getSymbol()) {
        ret = false;
        err = addError("Missing sort name from declare-sort command", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    if(!node->getArity()) {
        ret = false;
        err = addError("Missing sort arity from declare-sort command", node, err);
    } else {
        node->getArity()->accept(this);
    }
}

void SyntaxChecker::visit(DefineFunCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getDefinition()) {
        ret = false;
        err = addError("Missing function definition from define-fun command", node, err);
    } else {
        node->getDefinition()->accept(this);
    }
}

void SyntaxChecker::visit(DefineFunRecCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getDefinition()) {
        ret = false;
        err = addError("Missing function definition from define-fun-rec command", node, err);
    } else {
        node->getDefinition()->accept(this);
    }
}

void SyntaxChecker::visit(DefineFunsRecCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(node->getDeclarations().empty()) {
        ret = false;
        err = addError("Missing function declarations from define-funs-rec command", node, err);
    }

    if(node->getBodies().empty()) {
        ret = false;
        err = addError("Missing function bodies from define-funs-rec command", node, err);
    }

    if(node->getBodies().size() != node->getDeclarations().size()) {
        ret = false;
        err = addError("Number of function declarations is not equal to the number of function bodies in define-funs-rec command", node, err);
    }

    const std::vector<std::shared_ptr<FunctionDeclaration>> &decls = node->getDeclarations();
    for(std::vector<std::shared_ptr<FunctionDeclaration>>::const_iterator it = decls.begin();
        it != decls.end(); it++) {
        (*it)->accept(this);
    }

    const std::vector<std::shared_ptr<FunctionDeclaration>> &bodies = node->getDeclarations();
    for(std::vector<std::shared_ptr<FunctionDeclaration>>::const_iterator it = bodies.begin();
        it != bodies.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(DefineSortCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getSymbol()) {
        ret = false;
        err = addError("Missing sort name from define-sort command", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    const std::vector<std::shared_ptr<Symbol>> &params = node->getParams();
    for(std::vector<std::shared_ptr<Symbol>>::const_iterator it = params.begin(); it != params.end(); it++) {
        (*it)->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        err = addError("Missing sort from define-sort command", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(EchoCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(node->getMessage() == "") {
        err = addError("Attempting to echo empty string", node, err);
        ret = false;
    }

}

void SyntaxChecker::visit(ExitCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(GetAssertsCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(GetAssignsCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(GetInfoCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getFlag()) {
        ret = false;
        err = addError("Missing flag in get-info command", node, err);
    } else {
        node->getFlag()->accept(this);
    }
}

void SyntaxChecker::visit(GetModelCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(GetOptionCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getOption()) {
        ret = false;
        err = addError("Missing option in get-option command", node, err);
    } else {
        node->getOption()->accept(this);
    }
}

void SyntaxChecker::visit(GetProofCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(GetUnsatAssumsCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(GetUnsatCoreCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(GetValueCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(node->getTerms().empty()) {
        ret = false;
        err = addError("Missing terms in get-value command", node, err);
    } else {
        const std::vector<std::shared_ptr<Term>> &terms = node->getTerms();
        for (std::vector<std::shared_ptr<Term>>::const_iterator it = terms.begin(); it != terms.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(PopCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getNumeral()) {
        ret = false;
        err = addError("Missing numeral in pop command", node, err);
    } else {
        node->getNumeral()->accept(this);
    }
}

void SyntaxChecker::visit(PushCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getNumeral()) {
        ret = false;
        err = addError("Missing numeral in push command", node, err);
    } else {
        node->getNumeral()->accept(this);
    }
}

void SyntaxChecker::visit(ResetCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(ResetAssertsCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(SetInfoCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getInfo()) {
        ret = false;
        err = addError("Missing info in set-info command", node, err);
    } else {
        node->getInfo()->accept(this);
    }
}

void SyntaxChecker::visit(SetLogicCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getLogic()) {
        ret = false;
        err = addError("Missing logic in set-logic command", node, err);
    }
}

void SyntaxChecker::visit(SetOptionCommand const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getOption()) {
        ret = false;
        err = addError("Missing option in set-option command", node, err);
    } else {
        shared_ptr<Attribute> option = node->getOption();
        if((option->getKeyword()->getValue() == ":diagnostic-output-channel"
            || option->getKeyword()->getValue() == ":regular-output-channel")
           && !dynamic_cast<StringLiteral*>(option->getValue().get())) {
            ret = false;
            err = addError("Option value should be string literal", option.get(), err);
        } else if((option->getKeyword()->getValue() == ":random-seed"
                   || option->getKeyword()->getValue() == ":verbosity"
                   || option->getKeyword()->getValue() == ":reproducible-resource-limit")
                  && !dynamic_cast<NumeralLiteral*>(option->getValue().get())) {
            ret = false;
            err = addError("Option value should be numeral literal", option.get(), err);
        } else if((option->getKeyword()->getValue() == ":expand-definitions"
                   || option->getKeyword()->getValue() == ":global-declarations"
                   || option->getKeyword()->getValue() == ":interactive-mode"
                   || option->getKeyword()->getValue() == ":print-success"
                   || option->getKeyword()->getValue() == ":produce-assertions"
                   || option->getKeyword()->getValue() == ":produce-assignments"
                   || option->getKeyword()->getValue() == ":produce-models"
                   || option->getKeyword()->getValue() == ":produce-proofs"
                   || option->getKeyword()->getValue() == ":produce-unsat-assumptions"
                   || option->getKeyword()->getValue() == ":produce-unsat-cores")
                  && !dynamic_cast<BooleanValue*>(option->getValue().get())) {
            ret = false;
            err = addError("Option value should be boolean", option.get(), err);
        }

        node->getOption()->accept(this);
    }
}

void SyntaxChecker::visit(FunctionDeclaration const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getSymbol()) {
        ret = false;
        err = addError("Missing name from function declaration", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    const std::vector<std::shared_ptr<SortedVariable>> &params = node->getParams();
    for(std::vector<std::shared_ptr<SortedVariable>>::const_iterator it = params.begin(); it != params.end(); it++) {
        (*it)->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        err = addError("Missing return sort from function declaration", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(FunctionDefinition const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getSignature()) {
        ret = false;
        err = addError("Missing signature from function definition", node, err);
    } else {
        node->getSignature()->accept(this);
    }

    if(!node->getBody()) {
        ret = false;
        err = addError("Missing body from function definition", node, err);
    } else {
        node->getBody()->accept(this);
    }
}

void SyntaxChecker::visit(Identifier const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getSymbol()) {
        ret = false;
        err = addError("Missing symbol from identifier", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    if(node->isIndexed() && node->getIndices().empty()) {
        ret = false;
        err = addError("Indexed identifier has no indices", node, err);
    }

    const std::vector<std::shared_ptr<Index>> &indices = node->getIndices();
    for(std::vector<std::shared_ptr<Index>>::const_iterator it = indices.begin(); it != indices.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(QualifiedIdentifier const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from qualified identifier", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        err = addError("Missing sort from qualified identifier", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(DecimalLiteral const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(NumeralLiteral const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(StringLiteral const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 
 }

void SyntaxChecker::visit(Logic const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if(!node->getName()) {
        ret = false;
        err = addError("Missing logic name", node, err);
    }

    if(attrs.empty()) {
        ret = false;
        err = addError("Logic has no attributes", node, err);
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;
        if((attr->getKeyword()->getValue() == ":language"
            || attr->getKeyword()->getValue() == ":extensions"
            || attr->getKeyword()->getValue() == ":values"
            || attr->getKeyword()->getValue() == ":notes")
           && !dynamic_cast<StringLiteral*>(attr->getValue().get())) {
            ret = false;
            err = addError("Attribute value should be string literal", attr.get(), err);
        }

        if(attr->getKeyword()->getValue() == ":theories"
           && !dynamic_cast<CompoundAttributeValue*>(attr->getValue().get())) {
            ret = false;
            err = addError("Attribute value should be a list of theory names", attr.get(), err);
        } else {
            CompoundAttributeValue *val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            vector<shared_ptr<AttributeValue>> values = val->getValues();

            if(values.empty()) {
                ret = false;
                err = addError("Empty list of theory names", attr.get(), err);
            }

            for(vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                if(!dynamic_cast<Symbol*>((*itt).get())) {
                    ret = false;
                    err = addError("Attribute value should be a symbol", (*itt).get(), err);
                }
            }
        }

        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(Theory const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if(!node->getName()) {
        ret = false;
        err = addError("Missing theory name", node, err);
    }

    if(attrs.empty()) {
        ret = false;
        err = addError("Theory has no attributes", node, err);
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.end(); it++) {
        shared_ptr<Attribute> attr = *it;
        if((attr->getKeyword()->getValue() == ":sorts-description"
            || attr->getKeyword()->getValue() == ":funs-description"
            || attr->getKeyword()->getValue() == ":definition"
            || attr->getKeyword()->getValue() == ":values"
            || attr->getKeyword()->getValue() == ":notes")
           && !dynamic_cast<StringLiteral*>(attr->getValue().get())) {
            ret = false;
            err = addError("Attribute value should be string literal", attr.get(), err);
        }

        if((attr->getKeyword()->getValue() == ":sorts"
            || attr->getKeyword()->getValue() == ":funs")
           && !dynamic_cast<CompoundAttributeValue*>(attr->getValue().get())) {
            ret = false;
            if(attr->getKeyword()->getValue() == ":sorts")
                err = addError("Attribute value should be a list of sort symbol declarations", attr.get(), err);
            else
                err = addError("Attribute value should be a list of function symbol declarations", attr.get(), err);

        } else if(attr->getKeyword()->getValue() == ":sorts") {
            CompoundAttributeValue *val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            vector<shared_ptr<AttributeValue>> values = val->getValues();

            if(values.empty()) {
                ret = false;
                err = addError("Empty list of sort symbol declarations", attr.get(), err);
            }

            for(vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                if(!dynamic_cast<SortSymbolDeclaration*>((*itt).get())) {
                    ret = false;
                    err = addError("Attribute value should be a sort symbol declaration", (*itt).get(), err);
                }
            }
        } else if(attr->getKeyword()->getValue() == ":funs") {
            CompoundAttributeValue *val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            vector<shared_ptr<AttributeValue>> values = val->getValues();

            if(values.empty()) {
                ret = false;
                err = addError("Empty list of function symbol declarations", attr.get(), err);
            }

            for(vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                if(!dynamic_cast<FunSymbolDeclaration*>((*itt).get())) {
                    ret = false;
                    err = addError("Attribute value should be a function symbol declaration", (*itt).get(), err);
                }
            }
        }

        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(Script const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    const std::vector<std::shared_ptr<Command>> &commands = node->getCommands();
    for(std::vector<std::shared_ptr<Command>>::const_iterator it = commands.begin(); it != commands.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(Sort const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    if(!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from sort", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(node->isParametrized() && node->getParams().empty()) {
        ret = false;
        err = addError("Parametrized sort has no parameters", node, err);
    } else {
        const std::vector<std::shared_ptr<Sort>> &params = node->getParams();
        for (std::vector<std::shared_ptr<Sort>>::const_iterator it = params.begin(); it != params.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(CompSExpression const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	} 

    const std::vector<std::shared_ptr<SExpression>> &exprs = node->getExpressions();
    for(std::vector<std::shared_ptr<SExpression>>::const_iterator it = exprs.begin(); it != exprs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(SortSymbolDeclaration const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from sort symbol declaration", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(!node->getArity()) {
        ret = false;
        err = addError("Missing arity from sort symbol declaration", node, err);
    } else {
        node->getArity()->accept(this);
    }

    const std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for(std::vector<std::shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(SpecConstFunDeclaration const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getConstant()) {
        ret = false;
        err = addError("Missing constant from spec constant function symbol declaration", node, err);
    } else {
        node->getConstant()->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        err = addError("Missing sort from spec constant function symbol declaration", node, err);
    } else {
        node->getSort()->accept(this);
    }

    const std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for(std::vector<std::shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(MetaSpecConstFunDeclaration const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getConstant()) {
        ret = false;
        err = addError("Missing constant from meta spec constant function symbol declaration", node, err);
    } else {
        node->getConstant()->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        err = addError("Missing sort from meta spec constant function symbol declaration", node, err);
    } else {
        node->getSort()->accept(this);
    }

    const std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for(std::vector<std::shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(IdentifierFunDeclaration const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from function symbol declaration", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(node->getSignature().empty()) {
        ret = false;
        err = addError("Empty signature for function symbol declaration", node, err);
    } else {
        const std::vector<std::shared_ptr<Sort>> &sig = node->getSignature();
        for(std::vector<std::shared_ptr<Sort>>::const_iterator it = sig.begin(); it != sig.end(); it++) {
            (*it)->accept(this);
        }
    }

    const std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for(std::vector<std::shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(ParametricFunDeclaration const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from parametric function symbol declaration", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(node->getSignature().empty()) {
        ret = false;
        err = addError("Empty signature for parametric function symbol declaration", node, err);
    } else {
        const std::vector<std::shared_ptr<Sort>> &sig = node->getSignature();
        for(std::vector<std::shared_ptr<Sort>>::const_iterator it = sig.begin(); it != sig.end(); it++) {
            (*it)->accept(this);
        }
    }

    if(node->getParams().empty()) {
        ret = false;
        err = addError("Empty parameter list for parametric function symbol declaration", node, err);
    } else {
        const std::vector<std::shared_ptr<Symbol>> &params = node->getParams();
        for(std::vector<std::shared_ptr<Symbol>>::const_iterator it = params.begin(); it != params.end(); it++) {
            (*it)->accept(this);
        }
    }

    const std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for(std::vector<std::shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void SyntaxChecker::visit(QualifiedTerm const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getIdentifier()) {
        ret = false;
        err = addError("Missing identifier from qualified term", node, err);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(node->getTerms().empty()) {
        ret = false;
        err = addError("Empty term list for qualified term", node, err);
    } else {
        const std::vector<std::shared_ptr<Term>> &terms = node->getTerms();
        for(std::vector<std::shared_ptr<Term>>::const_iterator it = terms.begin(); it != terms.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(LetTerm const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getTerm()) {
        ret = false;
        err = addError("Missing term from let term", node, err);
    } else {
        node->getTerm()->accept(this);
    }

    if(node->getBindings().empty()) {
        ret = false;
        err = addError("Empty variable binding list for let term", node, err);
    } else {
        const std::vector<std::shared_ptr<VarBinding>> &bindings = node->getBindings();
        for(std::vector<std::shared_ptr<VarBinding>>::const_iterator it = bindings.begin(); it != bindings.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(ForallTerm const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getTerm()) {
        ret = false;
        err = addError("Missing term from forall term", node, err);
    } else {
        node->getTerm()->accept(this);
    }

    if(node->getBindings().empty()) {
        ret = false;
        err = addError("Empty variable binding list for forall term", node, err);
    } else {
        const std::vector<std::shared_ptr<SortedVariable>> &bindings = node->getBindings();
        for(std::vector<std::shared_ptr<SortedVariable>>::const_iterator it = bindings.begin(); it != bindings.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(ExistsTerm const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getTerm()) {
        ret = false;
        err = addError("Missing term from exists term", node, err);
    } else {
        node->getTerm()->accept(this);
    }

    if(node->getBindings().empty()) {
        ret = false;
        err = addError("Empty variable binding list for exists term", node, err);
    } else {
        const std::vector<std::shared_ptr<SortedVariable>> &bindings = node->getBindings();
        for(std::vector<std::shared_ptr<SortedVariable>>::const_iterator it = bindings.begin(); it != bindings.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(AnnotatedTerm const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getTerm()) {
        ret = false;
        err = addError("Missing term from annotated term", node, err);
    } else {
        node->getTerm()->accept(this);
    }

    if(node->getAttributes().empty()) {
        ret = false;
        err = addError("Empty attribute list for exists term", node, err);
    } else {
        const std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
        for(std::vector<std::shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void SyntaxChecker::visit(SortedVariable const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getSymbol()) {
        ret = false;
        err = addError("Missing symbol from sorted variable", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        err = addError("Missing sort from sorted variable", node, err);
    } else {
        node->getSort()->accept(this);
    }
}

void SyntaxChecker::visit(VarBinding const *node) {
	shared_ptr<SyntaxCheckError> err;

	if(!node) {
		err = addError("Attempt to visit NULL node", node, err);
		return;
	}

    if(!node->getSymbol()) {
        ret = false;
        err = addError("Missing symbol from variable binding", node, err);
    } else {
        node->getSymbol()->accept(this);
    }

    if(!node->getTerm()) {
        ret = false;
        err = addError("Missing sort from variable binding", node, err);
    } else {
        node->getTerm()->accept(this);
    }
}

string SyntaxChecker::getErrors() {
    stringstream ss;
    for(vector<shared_ptr<SyntaxCheckError>>::iterator it = errors.begin(); it != errors.end(); it++) {
        shared_ptr<SyntaxCheckError> err = *it;
        if(err->node) {
            ss << err->node->getRowLeft() << ":" << err->node->getColLeft()
               << " - " << err->node->getRowRight() << ":" << err->node->getColRight() << "   ";

            string nodestr = err->node->toString();
            if(nodestr.length() > 100)
                ss << string(nodestr, 100);
            else
                ss << nodestr;
        } else {
            ss << "NULL";
        }

        ss << endl;
        for(std::vector<std::string>::iterator itt = err->messages.begin(); itt != err->messages.end(); itt++) {
            ss << "\t" << *itt << "." << endl;
        }

        if (it + 1 != errors.end()) {
            ss << endl;
        }
    }

    return ss.str();
}