#include <vector>
#include <memory>

#include <visitor/ast_syntax_checker.h>
#include <ast/ast_attribute.h>
#include <ast/ast_command.h>
#include <ast/ast_theory.h>
#include <ast/ast_logic.h>
#include <ast/ast_symbol_decl.h>
#include <ast/ast_term.h>

using namespace std;
using namespace smtlib::ast;

void AstSyntaxChecker::visit(Attribute const *node) {
    if(!node->getKeyword())
        ret = false;
}

void AstSyntaxChecker::visit(CompoundAttributeValue const *node) { }

void AstSyntaxChecker::visit(Symbol const *node) {
    //TODO
}

void AstSyntaxChecker::visit(Keyword const *node) {
    //TODO
}

void AstSyntaxChecker::visit(MetaSpecConstant const *node) { }

void AstSyntaxChecker::visit(BooleanValue const *node) { }

void AstSyntaxChecker::visit(PropLiteral const *node) {
    if(!node->getSymbol())
        ret = false;
}

void AstSyntaxChecker::visit(AssertCommand const *node) {
    if(!node->getTerm())
        ret = false;
}

void AstSyntaxChecker::visit(CheckSatCommand const *node) { }

void AstSyntaxChecker::visit(CheckSatAssumCommand const *node) { }

void AstSyntaxChecker::visit(DeclareConstCommand const *node) {
    if(!node->getSymbol() || !node->getSort())
        ret = false;
}

void AstSyntaxChecker::visit(DeclareFunCommand const *node) {
    if(!node->getSymbol() || !node->getSort())
        ret = false;
}

void AstSyntaxChecker::visit(DeclareSortCommand const *node) {
    if(!node->getSymbol() || !node->getArity())
        ret = false;
}

void AstSyntaxChecker::visit(DefineFunCommand const *node) {
    if(!node->getDefinition())
        ret = false;
}

void AstSyntaxChecker::visit(DefineFunRecCommand const *node) {
    if(!node->getDefinition())
        ret = false;
}

void AstSyntaxChecker::visit(DefineFunsRecCommand const *node) {
    if(!node
       || node->getBodies().empty()
       || node->getDeclarations().empty()
       || node->getBodies().size() != node->getDeclarations().size())
        ret = false;
}

void AstSyntaxChecker::visit(DefineSortCommand const *node) {
    if(!node->getSymbol() || !node->getSort())
        ret = false;
}

void AstSyntaxChecker::visit(EchoCommand const *node) {
    if(node->getMessage() == "")
        ret = false;
}

void AstSyntaxChecker::visit(ExitCommand const *node) { }

void AstSyntaxChecker::visit(GetAssertsCommand const *node) { }

void AstSyntaxChecker::visit(GetAssignsCommand const *node) { }

void AstSyntaxChecker::visit(GetInfoCommand const *node) {
    if(!node->getFlag())
        ret = false;
}

void AstSyntaxChecker::visit(GetModelCommand const *node) { }

void AstSyntaxChecker::visit(GetOptionCommand const *node) {
    if(!node->getOption())
        ret = false;
}

void AstSyntaxChecker::visit(GetProofCommand const *node) { }

void AstSyntaxChecker::visit(GetUnsatAssumsCommand const *node) { }

void AstSyntaxChecker::visit(GetUnsatCoreCommand const *node) { }

void AstSyntaxChecker::visit(GetValueCommand const *node) {
    if(node->getTerms().empty())
        ret = false;
}

void AstSyntaxChecker::visit(PopCommand const *node) {
    if(!node->getNumeral())
        ret = false;
}

void AstSyntaxChecker::visit(PushCommand const *node) {
    if(!node->getNumeral())
        ret = false;
}

void AstSyntaxChecker::visit(ResetCommand const *node) { }

void AstSyntaxChecker::visit(ResetAssertsCommand const *node) { }

void AstSyntaxChecker::visit(SetInfoCommand const *node) {
    if(!node->getInfo())
        ret = false;
}

void AstSyntaxChecker::visit(SetLogicCommand const *node) {
    if(!node->getLogic())
        ret = false;
}

void AstSyntaxChecker::visit(SetOptionCommand const *node) {
    if(!node->getOption())
        ret = false;
    else {
        shared_ptr<Attribute> option = node->getOption();
        if((option->getKeyword()->getValue() == ":diagnostic-output-channel"
            || option->getKeyword()->getValue() == ":regular-output-channel")
           && !dynamic_cast<StringLiteral*>(option->getValue().get())) {
            ret = false;
        } else if((option->getKeyword()->getValue() == ":random-seed"
                   || option->getKeyword()->getValue() == ":verbosity"
                   || option->getKeyword()->getValue() == ":reproducible-resource-limit")
                  && !dynamic_cast<NumeralLiteral*>(option->getValue().get())) {
            ret = false;
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
        }
    }
}

void AstSyntaxChecker::visit(FunctionDeclaration const *node) {
    if(!node->getSymbol() || !node->getSort())
        ret = false;
}

void AstSyntaxChecker::visit(FunctionDefinition const *node) {
    if(!node->getBody() || !node->getSignature())
        ret = false;
}

void AstSyntaxChecker::visit(Identifier const *node) {
    if(node->getSymbol())
        ret = false;
    if(node->isIndexed() && node->getIndices().empty())
        ret = false;
}

void AstSyntaxChecker::visit(QualifiedIdentifier const *node) {
    if(!node->getIdentifier() || !node->getSort())
        ret = false;
}

void AstSyntaxChecker::visit(DecimalLiteral const *node) { }

void AstSyntaxChecker::visit(NumeralLiteral const *node) { }

void AstSyntaxChecker::visit(StringLiteral const *node) { }

void AstSyntaxChecker::visit(Logic const *node) {
    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if(attrs.empty() || !node->getName()) {
        ret = false;
    }

    for(vector<shared_ptr<Attribute>>::iterator it = attrs.begin(); it != attrs.begin(); it++) {
        shared_ptr<Attribute> attr = *it;
        if((attr->getKeyword()->getValue() == ":language"
            || attr->getKeyword()->getValue() == ":extensions"
            || attr->getKeyword()->getValue() == ":values"
            || attr->getKeyword()->getValue() == ":notes")
           && !dynamic_cast<StringLiteral*>(attr->getValue().get())) {
            ret = false;
        }

        if(attr->getKeyword()->getValue() == ":theories"
           && !dynamic_cast<CompoundAttributeValue*>(attr->getValue().get())) {
            ret = false;
        } else {
            CompoundAttributeValue *val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            vector<shared_ptr<AttributeValue>> values = val->getValues();

            if(values.empty())
                ret = false;

            for(vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                if(!dynamic_cast<Symbol*>((*itt).get()))
                    ret = false;
            }
        }
    }
}

void AstSyntaxChecker::visit(Theory const *node) {
    vector<shared_ptr<Attribute>> attrs = node->getAttributes();

    if(attrs.empty() || !node->getName()) {
        ret = false;
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
        }

        if((attr->getKeyword()->getValue() == ":sorts"
            || attr->getKeyword()->getValue() == ":funs")
           && !dynamic_cast<CompoundAttributeValue*>(attr->getValue().get())) {
            ret = false;
        } else if(attr->getKeyword()->getValue() == ":sorts") {
            CompoundAttributeValue *val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            vector<shared_ptr<AttributeValue>> values = val->getValues();

            if(values.empty())
                ret = false;

            for(vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                if(!dynamic_cast<SortSymbolDeclaration*>((*itt).get()))
                    ret = false;
            }
        } else if(attr->getKeyword()->getValue() == ":funs") {
            CompoundAttributeValue *val = dynamic_cast<CompoundAttributeValue*>(attr->getValue().get());
            vector<shared_ptr<AttributeValue>> values = val->getValues();

            if(values.empty())
                ret = false;

            for(vector<shared_ptr<AttributeValue>>::iterator itt = values.begin(); itt != values.begin(); itt++) {
                if(!dynamic_cast<FunSymbolDeclaration*>((*itt).get()))
                    ret = false;
            }
        }
    }
}

void AstSyntaxChecker::visit(Script const *node) { }

void AstSyntaxChecker::visit(Sort const *node) {
    if(node->getIdentifier())
        ret = false;
    if(node->isParametric() && node->getParams().empty())
        ret = false;
}

void AstSyntaxChecker::visit(CompSExpression const *node) { }

void AstSyntaxChecker::visit(SortSymbolDeclaration const *node) {
    if(!node->getIdentifier() || !node->getArity())
        ret = false;
}

void AstSyntaxChecker::visit(SpecConstFunDeclaration const *node) {
    if(!node->getConstant() || !node->getSort())
        ret = false;
}

void AstSyntaxChecker::visit(MetaSpecConstFunDeclaration const *node) {
    if(!node->getConstant() || !node->getSort())
        ret = false;
}

void AstSyntaxChecker::visit(IdentifierFunDeclaration const *node) {
    if(!node->getIdentifier() || node->getSignature().empty())
        ret = false;
}

void AstSyntaxChecker::visit(ParametricFunDeclaration const *node) {
    if(node->getParams().empty())
        ret = false;
}

void AstSyntaxChecker::visit(QualifiedTerm const *node) {
    if(!node->getIdentifier() || node->getTerms().empty())
        ret = false;
}

void AstSyntaxChecker::visit(LetTerm const *node) {
    if(!node->getTerm() || node->getBindings().empty())
        ret = false;
}

void AstSyntaxChecker::visit(ForallTerm const *node) {
    if(!node->getTerm() || node->getBindings().empty())
        ret = false;
}

void AstSyntaxChecker::visit(ExistsTerm const *node) {
    if(!node->getTerm() || node->getBindings().empty())
        ret = false;
}

void AstSyntaxChecker::visit(AnnotatedTerm const *node) {
    if(!node->getTerm() || node->getAttrs().empty())
        ret = false;
}

void AstSyntaxChecker::visit(SortedVariable const *node) {
    if(!node->getSymbol() || !node->getSort())
        ret = false;
}

void AstSyntaxChecker::visit(VarBinding const *node) {
    if(!node->getSymbol() || !node->getTerm())
        ret = false;
}