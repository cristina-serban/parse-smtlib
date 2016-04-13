#include <iostream>
#include <unordered_map>
#include <sstream>
#include "ast_predicate_unfolder.h"
#include "ast_node_duplicator.h"
#include "ast_var_replacer.h"
#include "../ast/ast_command.h"
#include "../ast/ast_logic.h"
#include "../ast/ast_script.h"
#include "../ast/ast_sexp.h"
#include "../ast/ast_symbol_decl.h"
#include "../ast/ast_theory.h"
#include "ast_term_replacer.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

void PredicateUnfolder::visit(std::shared_ptr<DefineFunRecCommand> node) {
    findCounter = 0;
    predLevel = 0;
    prevFind = -1;
    predLevelCounter = new int[ctx->getUnfoldLevel() + 1];

    for (int i = 0; i <= ctx->getUnfoldLevel(); i++) {
        predLevelCounter[i] = 0;
    }

    output.open(ctx->getOutputPath().c_str(), std::fstream::out | std::fstream::app);

    shared_ptr<QualifiedTerm> body = dynamic_pointer_cast<QualifiedTerm>(node->getDefinition()->getBody());
    currentBaseCase = dynamic_pointer_cast<Term>(body->getTerms()[0]);
    currentRecCase = dynamic_pointer_cast<ExistsTerm>(body->getTerms()[1]);

    shared_ptr<NodeDuplicator> dupl = make_shared<NodeDuplicator>();
    if (ctx->isExistential()) {
        currentDefinition = node->getDefinition();
    } else {
        currentDefinition = dynamic_pointer_cast<FunctionDefinition>(dupl->run(node->getDefinition()));
        body = dynamic_pointer_cast<QualifiedTerm>(currentDefinition->getBody());
        body->getTerms().pop_back();
        body->getTerms().push_back(currentRecCase->getTerm());

        for (shared_ptr<SortedVariable> binding : currentRecCase->getBindings()) {
            output << "(declare-const " << binding->getSymbol()->toString()
            << " " << binding->getSort()->toString() << ")" << endl;
        }
    }

    std::shared_ptr<Term> unfoldedBody = dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, body));

    shared_ptr<DefineFunRecCommand> cmd = dynamic_pointer_cast<DefineFunRecCommand>(dupl->run(node));
    cmd->getDefinition()->setBody(unfoldedBody);

    stringstream ss;
    ss << cmd->getDefinition()->getSignature()->getSymbol()->getValue() << ctx->getUnfoldLevel();
    if(ctx->isExistential())
        ss << "e";
    cmd->getDefinition()->getSignature()->getSymbol()->setValue(ss.str());

    shared_ptr<DefineFunCommand> res = make_shared<DefineFunCommand>(cmd->getDefinition());

    if(ctx->isCvcEmp()) {
        shared_ptr<SimpleIdentifier> emp = make_shared<SimpleIdentifier>(make_shared<Symbol>("emp"));
        shared_ptr<NumeralLiteral> zero = make_shared<NumeralLiteral>(0, 10);

        vector<shared_ptr<Term>> terms;
        terms.push_back(zero);
        shared_ptr<QualifiedTerm> emp0 = make_shared<QualifiedTerm>(emp, terms);

        shared_ptr<TermReplacerContext> ctx =
                make_shared<TermReplacerContext>(emp, emp0);
        shared_ptr<TermReplacer> repl = make_shared<TermReplacer>(ctx);
        res->getDefinition()->getBody()->accept(repl.get());
    }

    output << res->toString() << endl << endl;

    delete[] predLevelCounter;
    output.close();

    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<QualifiedTerm> node) {
    shared_ptr<FunctionDeclaration> signature = currentDefinition->getSignature();

    if (node->getIdentifier()->toString() == signature->getSymbol()->toString()) {

        if (prevFind < 0) {
            predLevel = 0;
        } else if (prevFind < arg) {
            predLevel++;
            predLevelCounter[predLevel] = 0;
        }

        prevFind = arg;

        shared_ptr<VariableReplacerContext> replaceContext = make_shared<VariableReplacerContext>();
        shared_ptr<VariableReplacer> renamer = make_shared<VariableReplacer>(replaceContext);

        shared_ptr<NodeDuplicator> dupl = make_shared<NodeDuplicator>();
        shared_ptr<AstNode> dup;

        if (ctx->getUnfoldLevel() == predLevel) {
            dup = dupl->run(currentBaseCase);
        } else {
            dup = dupl->run(currentDefinition->getBody());
            for (shared_ptr<SortedVariable> binding : currentRecCase->getBindings()) {
                string varName = binding->getSymbol()->toString();
                stringstream sss;
                sss << varName;

                for (int i = 0; i < predLevel; i++) {
                    sss << (predLevelCounter[i] - 1);
                }
                sss << predLevelCounter[predLevel];

                if (!ctx->isExistential())
                    output << "(declare-const " << sss.str() << " " << binding->getSort()->toString() << ")" << endl;

                replaceContext->getRenamingMap()[varName] = sss.str();
            }
            dup->accept(renamer.get());
        }

        replaceContext->getRenamingMap().clear();
        for (int i = 0; i < signature->getParams().size(); i++) {
            stringstream ss;
            ss << node->getTerms()[i]->toString();
            replaceContext->getRenamingMap()[signature->getParams()[i]->getSymbol()->toString()] = ss.str();
        }
        dup->accept(renamer.get());

        predLevelCounter[predLevel]++;
        findCounter++;

        if (ctx->getUnfoldLevel() > predLevel) {
            int oldPredLevel = predLevel;
            dup = wrappedVisit(arg + 1, dup);
            predLevel = oldPredLevel;
        }

        ret = dup;
    } else {
        node->setIdentifier(dynamic_pointer_cast<Identifier>(wrappedVisit(arg + 1, node->getIdentifier())));

        vector<shared_ptr<Term>> newTerms;
        for (shared_ptr<Term> term : node->getTerms()) {
            newTerms.push_back(dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, term)));
        }

        node->getTerms().clear();
        node->getTerms().insert(node->getTerms().begin(), newTerms.begin(), newTerms.end());

        ret = node;
    }
}

void PredicateUnfolder::visit(std::shared_ptr<Attribute> node) {
    wrappedVisit(arg + 1, node->getKeyword());
    wrappedVisit(arg + 1, node->getValue());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<CompAttributeValue> node) {
    for (shared_ptr<AttributeValue> it : node->getValues()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<Symbol> node) { ret = node; }

void PredicateUnfolder::visit(std::shared_ptr<Keyword> node) { ret = node; }

void PredicateUnfolder::visit(std::shared_ptr<MetaSpecConstant> node) { ret = node; }

void PredicateUnfolder::visit(std::shared_ptr<BooleanValue> node) { ret = node; }

void PredicateUnfolder::visit(std::shared_ptr<PropLiteral> node) { ret = node; }

void PredicateUnfolder::visit(std::shared_ptr<AssertCommand> node) {
    wrappedVisit(arg + 1, node->getTerm());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<CheckSatCommand> node) { ret = node; }

void PredicateUnfolder::visit(std::shared_ptr<CheckSatAssumCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<DeclareConstCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<DeclareDatatypeCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<DeclareDatatypesCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<DeclareFunCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<DeclareSortCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<DefineFunCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<DefineFunsRecCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<DefineSortCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<EchoCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<ExitCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<GetAssertsCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<GetAssignsCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<GetInfoCommand> node) {
    wrappedVisit(arg + 1, node->getFlag());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<GetModelCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<GetOptionCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<GetProofCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<GetUnsatAssumsCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<GetUnsatCoreCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<GetValueCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<PopCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<PushCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<ResetCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<ResetAssertsCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SetInfoCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SetLogicCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SetOptionCommand> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<FunctionDeclaration> node) {
    wrappedVisit(arg + 1, node->getSymbol());
    for (shared_ptr<SortedVariable> it : node->getParams()) {
        wrappedVisit(arg + 1, it);
    }
    wrappedVisit(arg + 1, node->getSort());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<FunctionDefinition> node) {
    wrappedVisit(arg + 1, node->getSignature());
    wrappedVisit(arg + 1, node->getBody());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SimpleIdentifier> node) {
    wrappedVisit(arg + 1, node->getSymbol());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<QualifiedIdentifier> node) {
    wrappedVisit(arg + 1, node->getIdentifier());
    wrappedVisit(arg + 1, node->getSort());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<DecimalLiteral> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<NumeralLiteral> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<StringLiteral> node) {
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<Logic> node) {
    wrappedVisit(arg + 1, node->getName());
    for (shared_ptr<Attribute> it : node->getAttributes()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<Theory> node) {
    wrappedVisit(arg + 1, node->getName());
    for (shared_ptr<Attribute> it : node->getAttributes()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<Script> node) {
    for (shared_ptr<Command> it : node->getCommands()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<Sort> node) {
    wrappedVisit(arg + 1, node->getIdentifier());
    for (shared_ptr<Sort> it : node->getArgs()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<CompSExpression> node) {
    for (shared_ptr<SExpression> it : node->getExpressions()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SortSymbolDeclaration> node) {
    wrappedVisit(arg + 1, node->getIdentifier());
    wrappedVisit(arg + 1, node->getArity());
    for (shared_ptr<Attribute> it : node->getAttributes()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SortDeclaration> node) {
    wrappedVisit(arg + 1, node->getSymbol());
    wrappedVisit(arg + 1, node->getArity());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SelectorDeclaration> node) {
    wrappedVisit(arg + 1, node->getSymbol());
    wrappedVisit(arg + 1, node->getSort());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<ConstructorDeclaration> node) {
    wrappedVisit(arg + 1, node->getSymbol());
    for (shared_ptr<SelectorDeclaration> it : node->getSelectors()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SimpleDatatypeDeclaration> node) {
    for (shared_ptr<ConstructorDeclaration> it : node->getConstructors()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<ParametricDatatypeDeclaration> node) {
    for (shared_ptr<ConstructorDeclaration> it : node->getConstructors()) {
        wrappedVisit(arg + 1, it);
    }
    for (shared_ptr<Symbol> it : node->getParams()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<QualifiedConstructor> node) {
    wrappedVisit(arg + 1, node->getSymbol());
    wrappedVisit(arg + 1, node->getSort());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<QualifiedPattern> node) {
    wrappedVisit(arg + 1, node->getConstructor());
    for (shared_ptr<Symbol> it : node->getSymbols()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<MatchCase> node) {
    wrappedVisit(arg + 1, node->getPattern());
    wrappedVisit(arg + 1, node->getTerm());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SpecConstFunDeclaration> node) {
    wrappedVisit(arg + 1, node->getConstant());
    wrappedVisit(arg + 1, node->getSort());
    for (shared_ptr<Attribute> it : node->getAttributes()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<MetaSpecConstFunDeclaration> node) {
    wrappedVisit(arg + 1, node->getConstant());
    wrappedVisit(arg + 1, node->getSort());
    for (shared_ptr<Attribute> it : node->getAttributes()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SimpleFunDeclaration> node) {
    wrappedVisit(arg + 1, node->getIdentifier());
    for (shared_ptr<Sort> it : node->getSignature()) {
        wrappedVisit(arg + 1, it);
    }
    for (shared_ptr<Attribute> it : node->getAttributes()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<ParametricFunDeclaration> node) {
    for (shared_ptr<Symbol> it : node->getParams()) {
        wrappedVisit(arg + 1, it);
    }
    wrappedVisit(arg + 1, node->getIdentifier());
    for (shared_ptr<Sort> it : node->getSignature()) {
        wrappedVisit(arg + 1, it);
    }
    for (shared_ptr<Attribute> it : node->getAttributes()) {
        wrappedVisit(arg + 1, it);
    }
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<LetTerm> node) {
    node->setTerm(dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->getTerm())));
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<ForallTerm> node) {
    node->setTerm(dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->getTerm())));
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<ExistsTerm> node) {
    node->setTerm(dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->getTerm())));
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<MatchTerm> node) {
    node->setTerm(dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->getTerm())));
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<AnnotatedTerm> node) {
    node->setTerm(dynamic_pointer_cast<Term>(wrappedVisit(arg + 1, node->getTerm())));
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<SortedVariable> node) {
    wrappedVisit(arg + 1, node->getSymbol());
    wrappedVisit(arg + 1, node->getSort());
    ret = node;
}

void PredicateUnfolder::visit(std::shared_ptr<VarBinding> node) {
    wrappedVisit(arg + 1, node->getSymbol());
    wrappedVisit(arg + 1, node->getTerm());
    ret = node;
}