#include "ast_syntax_checker.h"
#include "../ast/ast_attribute.h"
#include "../ast/ast_command.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_sexp.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_term.h"
#include "../ast/ast_theory.h"

#include <memory>
#include <regex>
#include <vector>

using namespace std;
using namespace smtlib::ast;

void AstSyntaxChecker::addError(string message, AstNode const *node) {
    shared_ptr<SyntaxCheckError> err = make_shared<SyntaxCheckError>();
    err->message = message;
    err->node = node;
    errors.push_back(err);
}

void AstSyntaxChecker::visit(Attribute const *node) {
    if(!node) {
        addError("Attempt to visit NULL node", node);
        return;
    }

    if(!node->getKeyword()) {
        ret = false;
        addError("Missing keyword from attribute", node);
    } else {
        node->getKeyword()->accept(this);
    }

    if(node->getValue())
        node->getValue()->accept(this);
}

void AstSyntaxChecker::visit(CompoundAttributeValue const *node) {
    if(!node) {
        addError("Attempt to visit NULL node", node);
        return;
    }

    const std::vector<std::shared_ptr<AttributeValue>> &vals = node->getValues();
    for(std::vector<std::shared_ptr<AttributeValue>>::const_iterator it = vals.begin(); it != vals.end(); it++) {
        (*it)->accept(this);
    }
}

void AstSyntaxChecker::visit(Symbol const *node) {
    if(!node) {
        addError("Attempt to visit NULL node", node);
        return;
    }

    if(!std::regex_match(node->getValue(), regexSymbol)) {
        ret = false;
        addError("Malformed symbol", node);
    }
}

void AstSyntaxChecker::visit(Keyword const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(MetaSpecConstant const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(BooleanValue const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(PropLiteral const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getSymbol()) {
        ret = false;
        addError("Missing symbol from propositional literal", node);
    } else {
        node->getSymbol()->accept(this);
    }
}

void AstSyntaxChecker::visit(AssertCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getTerm()) {
        ret = false;
        addError("Missing term from assert command", node);
    } else {
        node->getTerm()->accept(this);
    }
}

void AstSyntaxChecker::visit(CheckSatCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
}

void AstSyntaxChecker::visit(CheckSatAssumCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    const std::vector<std::shared_ptr<PropLiteral>> &assums = node->getAssumptions();
    for(std::vector<std::shared_ptr<PropLiteral>>::const_iterator it = assums.begin(); it != assums.end(); it++) {
        (*it)->accept(this);
    }
}

void AstSyntaxChecker::visit(DeclareConstCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getSymbol()) {
        ret = false;
        addError("Missing constant name from declare-const command", node);
    } else {
        node->getSymbol()->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        addError("Missing constant sort from declare-const command", node);
    } else {
        node->getSort()->accept(this);
    }
}

void AstSyntaxChecker::visit(DeclareFunCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getSymbol()) {
        ret = false;
        addError("Missing function name from declare-fun command", node);
    } else {
        node->getSymbol()->accept(this);
    }

    const std::vector<std::shared_ptr<Sort>> &params = node->getParams();
    for(std::vector<std::shared_ptr<Sort>>::const_iterator it = params.begin(); it != params.end(); it++) {
        (*it)->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        addError("Missing function sort from declare-fun command", node);
    } else {
        node->getSort()->accept(this);
    }
}

void AstSyntaxChecker::visit(DeclareSortCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getSymbol()) {
        ret = false;
        addError("Missing sort name from declare-sort command", node);
    } else {
        node->getSymbol()->accept(this);
    }

    if(!node->getArity()) {
        ret = false;
        addError("Missing sort arity from declare-sort command", node);
    } else {
        node->getArity()->accept(this);
    }
}

void AstSyntaxChecker::visit(DefineFunCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getDefinition()) {
        ret = false;
        addError("Missing function definition from define-fun command", node);
    } else {
        node->getDefinition()->accept(this);
    }
}

void AstSyntaxChecker::visit(DefineFunRecCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getDefinition()) {
        ret = false;
        addError("Missing function definition from define-fun-rec command", node);
    } else {
        node->getDefinition()->accept(this);
    }
}

void AstSyntaxChecker::visit(DefineFunsRecCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(node->getDeclarations().empty()) {
        ret = false;
        addError("Missing function declarations from define-funs-rec command", node);
    }

    if(node->getBodies().empty()) {
        ret = false;
        addError("Missing function bodies from define-funs-rec command", node);
    }

    if(node->getBodies().size() != node->getDeclarations().size()) {
        ret = false;
        addError("Number of function declarations is not equal to the number of function bodies in define-funs-rec command", node);
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

void AstSyntaxChecker::visit(DefineSortCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getSymbol()) {
        ret = false;
        addError("Missing sort name from define-sort command", node);
    } else {
        node->getSymbol()->accept(this);
    }

    const std::vector<std::shared_ptr<Symbol>> &params = node->getParams();
    for(std::vector<std::shared_ptr<Symbol>>::const_iterator it = params.begin(); it != params.end(); it++) {
        (*it)->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        addError("Missing sort from define-sort command", node);
    } else {
        node->getSort()->accept(this);
    }
}

void AstSyntaxChecker::visit(EchoCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(node->getMessage() == "") {
        addError("Attempting to echo empty string", node);
        ret = false;
    }

}

void AstSyntaxChecker::visit(ExitCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(GetAssertsCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(GetAssignsCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(GetInfoCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getFlag()) {
        ret = false;
        addError("Missing flag in get-info command", node);
    } else {
        node->getFlag()->accept(this);
    }
}

void AstSyntaxChecker::visit(GetModelCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(GetOptionCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getOption()) {
        ret = false;
        addError("Missing option in get-option command", node);
    } else {
        node->getOption()->accept(this);
    }
}

void AstSyntaxChecker::visit(GetProofCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(GetUnsatAssumsCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(GetUnsatCoreCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(GetValueCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(node->getTerms().empty()) {
        ret = false;
        addError("Missing terms in get-value command", node);
    } else {
        const std::vector<std::shared_ptr<Term>> &terms = node->getTerms();
        for (std::vector<std::shared_ptr<Term>>::const_iterator it = terms.begin(); it != terms.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void AstSyntaxChecker::visit(PopCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getNumeral()) {
        ret = false;
        addError("Missing numeral in pop command", node);
    } else {
        node->getNumeral()->accept(this);
    }
}

void AstSyntaxChecker::visit(PushCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getNumeral()) {
        ret = false;
        addError("Missing numeral in push command", node);
    } else {
        node->getNumeral()->accept(this);
    }
}

void AstSyntaxChecker::visit(ResetCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(ResetAssertsCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(SetInfoCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getInfo()) {
        ret = false;
        addError("Missing info in set-info command", node);
    } else {
        node->getInfo()->accept(this);
    }
}

void AstSyntaxChecker::visit(SetLogicCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getLogic()) {
        ret = false;
        addError("Missing logic in set-logic command", node);
    }
}

void AstSyntaxChecker::visit(SetOptionCommand const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getOption()) {
        ret = false;
        addError("Missing option in set-option command", node);
    } else {
        shared_ptr<Attribute> option = node->getOption();
        if((option->getKeyword()->getValue() == ":diagnostic-output-channel"
            || option->getKeyword()->getValue() == ":regular-output-channel")
           && !dynamic_cast<StringLiteral*>(option->getValue().get())) {
            ret = false;
            addError("Option value should be string literal", option.get());
        } else if((option->getKeyword()->getValue() == ":random-seed"
                   || option->getKeyword()->getValue() == ":verbosity"
                   || option->getKeyword()->getValue() == ":reproducible-resource-limit")
                  && !dynamic_cast<NumeralLiteral*>(option->getValue().get())) {
            ret = false;
            addError("Option value should be numeral literal", option.get());
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
            addError("Option value should be boolean", option.get());
        }

        node->getOption()->accept(this);
    }
}

void AstSyntaxChecker::visit(FunctionDeclaration const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getSymbol()) {
        ret = false;
        addError("Missing name from function declaration", node);
    } else {
        node->getSymbol()->accept(this);
    }

    const std::vector<std::shared_ptr<SortedVariable>> &params = node->getParams();
    for(std::vector<std::shared_ptr<SortedVariable>>::const_iterator it = params.begin(); it != params.end(); it++) {
        (*it)->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        addError("Missing return sort from function declaration", node);
    } else {
        node->getSort()->accept(this);
    }
}

void AstSyntaxChecker::visit(FunctionDefinition const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getSignature()) {
        ret = false;
        addError("Missing signature from function definition", node);
    } else {
        node->getSignature()->accept(this);
    }

    if(!node->getBody()) {
        ret = false;
        addError("Missing body from function definition", node);
    } else {
        node->getBody()->accept(this);
    }
}

void AstSyntaxChecker::visit(Identifier const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getSymbol()) {
        ret = false;
        addError("Missing symbol from identifier", node);
    } else {
        node->getSymbol()->accept(this);
    }

    if(node->isIndexed() && node->getIndices().empty()) {
        ret = false;
        addError("Indexed identifier has no indices", node);
    }

    const std::vector<std::shared_ptr<Index>> &indices = node->getIndices();
    for(std::vector<std::shared_ptr<Index>>::const_iterator it = indices.begin(); it != indices.end(); it++) {
        (*it)->accept(this);
    }
}

void AstSyntaxChecker::visit(QualifiedIdentifier const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getIdentifier()) {
        ret = false;
        addError("Missing identifier from qualified identifier", node);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        addError("Missing sort from qualified identifier", node);
    } else {
        node->getSort()->accept(this);
    }
}

void AstSyntaxChecker::visit(DecimalLiteral const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(NumeralLiteral const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(StringLiteral const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 
 }

void AstSyntaxChecker::visit(Logic const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if(!node->getName()) {
        ret = false;
        addError("Missing logic name", node);
    }

    if(attrs.empty()) {
        ret = false;
        addError("Logic has no attributes", node);
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.begin(); it++) {
        shared_ptr<Attribute> attr = *it;
        if((attr->getKeyword()->getValue() == ":language"
            || attr->getKeyword()->getValue() == ":extensions"
            || attr->getKeyword()->getValue() == ":values"
            || attr->getKeyword()->getValue() == ":notes")
           && !dynamic_cast<StringLiteral*>(attr->getValue().get())) {
            ret = false;
            addError("Attribute value should be string literal", attr.get());
        }

        if(attr->getKeyword()->getValue() == ":theories"
           && !dynamic_cast<CompoundAttributeValue*>(attr->getValue().get())) {
            ret = false;
            addError("Attribute value should be a list of theory names", attr.get());
        } else {
            CompoundAttributeValue *val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            vector<shared_ptr<AttributeValue>> values = val->getValues();

            if(values.empty()) {
                ret = false;
                addError("Empty list of theory names", attr.get());
            }

            for(vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                if(!dynamic_cast<Symbol*>((*itt).get())) {
                    ret = false;
                    addError("Attribute value should be a symbol", (*itt).get());
                }
            }
        }

        (*it)->accept(this);
    }
}

void AstSyntaxChecker::visit(Theory const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if(!node->getName()) {
        ret = false;
        addError("Missing theory name", node);
    }

    if(attrs.empty()) {
        ret = false;
        addError("Theory has no attributes", node);
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.begin(); it++) {
        shared_ptr<Attribute> attr = *it;
        if((attr->getKeyword()->getValue() == ":sorts-description"
            || attr->getKeyword()->getValue() == ":funs-description"
            || attr->getKeyword()->getValue() == ":definition"
            || attr->getKeyword()->getValue() == ":values"
            || attr->getKeyword()->getValue() == ":notes")
           && !dynamic_cast<StringLiteral*>(attr->getValue().get())) {
            ret = false;
            addError("Attribute value should be string literal", attr.get());
        }

        if((attr->getKeyword()->getValue() == ":sorts"
            || attr->getKeyword()->getValue() == ":funs")
           && !dynamic_cast<CompoundAttributeValue*>(attr->getValue().get())) {
            ret = false;
            if(attr->getKeyword()->getValue() == ":sorts")
                addError("Attribute value should be a list of sort symbol declarations", attr.get());
            else
                addError("Attribute value should be a list of function symbol declarations", attr.get());

        } else if(attr->getKeyword()->getValue() == ":sorts") {
            CompoundAttributeValue *val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            vector<shared_ptr<AttributeValue>> values = val->getValues();

            if(values.empty()) {
                ret = false;
                addError("Empty list of sort symbol declarations", attr.get());
            }

            for(vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                if(!dynamic_cast<SortSymbolDeclaration*>((*itt).get())) {
                    ret = false;
                    addError("Attribute value should be a sort symbol declaration", (*itt).get());
                }
            }
        } else if(attr->getKeyword()->getValue() == ":funs") {
            CompoundAttributeValue *val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            vector<shared_ptr<AttributeValue>> values = val->getValues();

            if(values.empty()) {
                ret = false;
                addError("Empty list of function symbol declarations", attr.get());
            }

            for(vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                if(!dynamic_cast<FunSymbolDeclaration*>((*itt).get())) {
                    ret = false;
                    addError("Attribute value should be a function symbol declaration", (*itt).get());
                }
            }
        }

        (*it)->accept(this);
    }
}

void AstSyntaxChecker::visit(Script const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    const std::vector<std::shared_ptr<Command>> &commands = node->getCommands();
    for(std::vector<std::shared_ptr<Command>>::const_iterator it = commands.begin(); it != commands.end(); it++) {
        (*it)->accept(this);
    }
}

void AstSyntaxChecker::visit(Sort const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    if(!node->getIdentifier()) {
        ret = false;
        addError("Missing identifier from sort", node);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(node->isParametrized() && node->getParams().empty()) {
        ret = false;
        addError("Parametrized sort has no parameters", node);
    } else {
        const std::vector<std::shared_ptr<Sort>> &params = node->getParams();
        for (std::vector<std::shared_ptr<Sort>>::const_iterator it = params.begin(); it != params.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void AstSyntaxChecker::visit(CompSExpression const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	} 

    const std::vector<std::shared_ptr<SExpression>> &exprs = node->getExpressions();
    for(std::vector<std::shared_ptr<SExpression>>::const_iterator it = exprs.begin(); it != exprs.end(); it++) {
        (*it)->accept(this);
    }
}

void AstSyntaxChecker::visit(SortSymbolDeclaration const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getIdentifier()) {
        ret = false;
        addError("Missing identifier from sort symbol declaration", node);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(!node->getArity()) {
        ret = false;
        addError("Missing arity from sort symbol declaration", node);
    } else {
        node->getArity()->accept(this);
    }

    const std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for(std::vector<std::shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void AstSyntaxChecker::visit(SpecConstFunDeclaration const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getConstant()) {
        ret = false;
        addError("Missing constant from spec constant function symbol declaration", node);
    } else {
        node->getConstant()->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        addError("Missing sort from spec constant function symbol declaration", node);
    } else {
        node->getSort()->accept(this);
    }

    const std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for(std::vector<std::shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void AstSyntaxChecker::visit(MetaSpecConstFunDeclaration const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getConstant()) {
        ret = false;
        addError("Missing constant from meta spec constant function symbol declaration", node);
    } else {
        node->getConstant()->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        addError("Missing sort from meta spec constant function symbol declaration", node);
    } else {
        node->getSort()->accept(this);
    }

    const std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
    for(std::vector<std::shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
        (*it)->accept(this);
    }
}

void AstSyntaxChecker::visit(IdentifierFunDeclaration const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getIdentifier()) {
        ret = false;
        addError("Missing identifier from function symbol declaration", node);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(node->getSignature().empty()) {
        ret = false;
        addError("Empty signature for function symbol declaration", node);
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

void AstSyntaxChecker::visit(ParametricFunDeclaration const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getIdentifier()) {
        ret = false;
        addError("Missing identifier from parametric function symbol declaration", node);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(node->getSignature().empty()) {
        ret = false;
        addError("Empty signature for parametric function symbol declaration", node);
    } else {
        const std::vector<std::shared_ptr<Sort>> &sig = node->getSignature();
        for(std::vector<std::shared_ptr<Sort>>::const_iterator it = sig.begin(); it != sig.end(); it++) {
            (*it)->accept(this);
        }
    }

    if(node->getParams().empty()) {
        ret = false;
        addError("Empty parameter list for parametric function symbol declaration", node);
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

void AstSyntaxChecker::visit(QualifiedTerm const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getIdentifier()) {
        ret = false;
        addError("Missing identifier from qualified term", node);
    } else {
        node->getIdentifier()->accept(this);
    }

    if(node->getTerms().empty()) {
        ret = false;
        addError("Empty term list for qualified term", node);
    } else {
        const std::vector<std::shared_ptr<Term>> &terms = node->getTerms();
        for(std::vector<std::shared_ptr<Term>>::const_iterator it = terms.begin(); it != terms.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void AstSyntaxChecker::visit(LetTerm const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getTerm()) {
        ret = false;
        addError("Missing term from let term", node);
    } else {
        node->getTerm()->accept(this);
    }

    if(node->getBindings().empty()) {
        ret = false;
        addError("Empty variable binding list for let term", node);
    } else {
        const std::vector<std::shared_ptr<VarBinding>> &bindings = node->getBindings();
        for(std::vector<std::shared_ptr<VarBinding>>::const_iterator it = bindings.begin(); it != bindings.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void AstSyntaxChecker::visit(ForallTerm const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getTerm()) {
        ret = false;
        addError("Missing term from forall term", node);
    } else {
        node->getTerm()->accept(this);
    }

    if(node->getBindings().empty()) {
        ret = false;
        addError("Empty variable binding list for forall term", node);
    } else {
        const std::vector<std::shared_ptr<SortedVariable>> &bindings = node->getBindings();
        for(std::vector<std::shared_ptr<SortedVariable>>::const_iterator it = bindings.begin(); it != bindings.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void AstSyntaxChecker::visit(ExistsTerm const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getTerm()) {
        ret = false;
        addError("Missing term from exists term", node);
    } else {
        node->getTerm()->accept(this);
    }

    if(node->getBindings().empty()) {
        ret = false;
        addError("Empty variable binding list for exists term", node);
    } else {
        const std::vector<std::shared_ptr<SortedVariable>> &bindings = node->getBindings();
        for(std::vector<std::shared_ptr<SortedVariable>>::const_iterator it = bindings.begin(); it != bindings.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void AstSyntaxChecker::visit(AnnotatedTerm const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getTerm()) {
        ret = false;
        addError("Missing term from annotated term", node);
    } else {
        node->getTerm()->accept(this);
    }

    if(node->getAttributes().empty()) {
        ret = false;
        addError("Empty attribute list for exists term", node);
    } else {
        const std::vector<std::shared_ptr<Attribute>> &attrs = node->getAttributes();
        for(std::vector<std::shared_ptr<Attribute>>::const_iterator it = attrs.begin(); it != attrs.end(); it++) {
            (*it)->accept(this);
        }
    }
}

void AstSyntaxChecker::visit(SortedVariable const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getSymbol()) {
        ret = false;
        addError("Missing symbol from sorted variable", node);
    } else {
        node->getSymbol()->accept(this);
    }

    if(!node->getSort()) {
        ret = false;
        addError("Missing sort from sorted variable", node);
    } else {
        node->getSort()->accept(this);
    }
}

void AstSyntaxChecker::visit(VarBinding const *node) {
	if(!node) {
		addError("Attempt to visit NULL node", node);
		return;
	}

    if(!node->getSymbol()) {
        ret = false;
        addError("Missing symbol from variable binding", node);
    } else {
        node->getSymbol()->accept(this);
    }

    if(!node->getTerm()) {
        ret = false;
        addError("Missing sort from variable binding", node);
    } else {
        node->getTerm()->accept(this);
    }
}