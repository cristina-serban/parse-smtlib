#include <memory>
#include <string>
#include <vector>
#include "smtlib-glue.h"

#include "smt_attribute.h"
#include "smt_basic.h"
#include "smt_command.h"
#include "smt_fun.h"
#include "smt_identifier.h"
#include "smt_literal.h"
#include "smt_logic.h"
#include "smt_s_expr.h"
#include "smt_script.h"
#include "smt_sort.h"
#include "smt_symbol_decl.h"
#include "smt_term.h"
#include "smt_theory.h"
#include "smt_var.h"

namespace smt {
    namespace ast {

        class ParserInternalList {
        private:
            std::vector<SmtPtr> v;
        public:
            template<class T>
            std::vector<std::shared_ptr<T>> unwrap() {
                std::vector<std::shared_ptr<T>> result;
                for (unsigned long i = 0, n = v.size(); i < n; ++i) {
                    result.push_back(std::shared_ptr<T>(dynamic_cast<T*>(v[i])));
                }
                v.clear();
                return result;
            };

            inline void add(SmtPtr item) {
                v.push_back(item);
            }
        };
    }
}

using namespace smt::ast;

template<class T>
std::shared_ptr<T> share(SmtPtr nakedPtr) {
    return std::shared_ptr<T>(dynamic_cast<T*>(nakedPtr));
}

SmtList smt_listCreate() {
    return new ParserInternalList();
}

void smt_listAdd(SmtList list, SmtPtr item) {
    list->add(item);
}

void smt_listDelete(SmtList list) {
    delete list;
}

// smt_attribute.h
SmtPtr smt_newAttribute1(SmtPtr keyword) {
    return new Attribute(share<Keyword>(keyword));
}

SmtPtr smt_newAttribute2(SmtPtr keyword, SmtPtr attr_value) {
    return new Attribute(
            share<Keyword>(keyword),
            share<IAttributeValue>(attr_value)
    );
}

// smt_basic.h
SmtPtr smt_newKeyword(char const* value) {
    return new Keyword(value);
}

SmtPtr smt_newMetaSpecConstant(int value) {
    return new MetaSpecConstant(static_cast<MetaSpecConstant::Type>(value));
}

SmtPtr smt_newBooleanValue(bool value) {
    return new BooleanValue(value);
}

SmtPtr smt_newPropLiteral(SmtPtr symbol, bool negated) {
    return new PropLiteral(share<Symbol>(symbol), negated);
}

// smt_command.h
SmtPtr smt_newAssertCommand(SmtPtr term) {
    return new AssertCommand(share<ITerm>(term));
}

SmtPtr smt_newCheckSatCommand() {
    return new CheckSatCommand();
}

SmtPtr smt_newCheckSatAssumCommand(SmtList assumptions) {
    return new CheckSatAssumCommand(assumptions->unwrap<PropLiteral>());
}

SmtPtr smt_newDeclareConstCommand(SmtPtr symbol, SmtPtr sort) {
    return new DeclareConstCommand(share<Symbol>(symbol), share<Sort>(sort));
}

SmtPtr smt_newDeclareFunCommand(SmtPtr symbol, SmtList params, SmtPtr sort) {
    return new DeclareFunCommand(share<Symbol>(symbol),
                                 params->unwrap<Sort>(),
                                 share<Sort>(sort));
}

SmtPtr smt_newDeclareSortCommand(SmtPtr symbol, SmtPtr arity) {
    return new DeclareSortCommand(share<Symbol>(symbol), share<NumeralLiteral>(arity));
}

SmtPtr smt_newDefineFunCommand(SmtPtr definition) {
    return new DefineFunCommand(share<FunctionDefinition>(definition));
}

SmtPtr smt_newDefineFunRecCommand(SmtPtr definition) {
    return new DefineFunRecCommand(share<FunctionDefinition>(definition));
}

SmtPtr smt_newDefineFunsRecCommand(SmtList definitions) {
    return new DefineFunsRecCommand(definitions->unwrap<FunctionDefinition>());
}

SmtPtr smt_newDefineSortCommand(SmtPtr symbol, SmtList params, SmtPtr sort) {
    return new DefineSortCommand(share<Symbol>(symbol),
                                 params->unwrap<Symbol>(),
                                 share<Sort>(sort));
}

SmtPtr smt_newEchoCommand(char const* msg) {
    return new EchoCommand(msg);
}

SmtPtr smt_newExitCommand() {
    return new ExitCommand();
}

SmtPtr smt_newGetAssertsCommand() {
    return new GetAssertsCommand();
}

SmtPtr smt_newGetAssignsCommand() {
    return new GetAssignsCommand();
}

SmtPtr smt_newGetInfoCommand(SmtPtr keyword) {
    return new GetInfoCommand(share<Keyword>(keyword));
}

SmtPtr smt_newGetModelCommand() {
    return new GetModelCommand();
}

SmtPtr smt_newGetOptionCommand(SmtPtr keyword) {
    return new GetOptionCommand(share<Keyword>(keyword));
}

SmtPtr smt_newGetProofCommand() {
    return new GetProofCommand();
}

SmtPtr smt_newGetUnsatAssumsCommand() {
    return new GetUnsatAssumsCommand();
}

SmtPtr smt_newGetUnsatCoreCommand() {
    return new GetUnsatCoreCommand();
}

SmtPtr smt_newGetValueCommand(SmtList terms);

SmtPtr smt_newPopCommand(SmtPtr numeral) {
    return new PopCommand(share<NumeralLiteral>(numeral));
}

SmtPtr smt_newPushCommand(SmtPtr numeral) {
    return new PushCommand(share<NumeralLiteral>(numeral));
}
SmtPtr smt_newResetCommand() {
    return new ResetCommand();
}

SmtPtr smt_newResetAssertsCommand() {
    return new ResetAssertsCommand();
}

SmtPtr smt_newSetInfoCommand(SmtPtr info) {
    return new SetInfoCommand(share<Attribute>(info));
}

SmtPtr smt_newSetLogicCommand(SmtPtr logic) {
    return new SetLogicCommand(share<Symbol>(logic));
}

SmtPtr smt_newSetOptionCommand(SmtPtr option) {
    return new SetOptionCommand(share<Attribute>(option));
}

// smt_fun.h
SmtPtr smt_newFunctionDeclaration(SmtPtr symbol, SmtList params, SmtPtr sort) {
    return new FunctionDeclaration(share<Symbol>(symbol), params->unwrap<SortedVariable>(), share<Sort>(sort));
}

SmtPtr smt_newFunctionDefinition(SmtPtr signature, SmtPtr body) {
    return new FunctionDefinition(share<FunctionDeclaration>(signature), share<ITerm>(body));
}

// smt_identifier.h
SmtPtr smt_newIdentifier1(SmtPtr symbol) {
    return new Identifier(share<Symbol>(symbol));
}

SmtPtr smt_newIdentifier2(SmtPtr symbol, SmtList indices) {
    return new Identifier(share<Symbol>(symbol),
                          indices->unwrap<IIndex>());
}

SmtPtr smt_newQualifiedIdentifier(SmtPtr identifier, SmtPtr sort) {
    return new QualifiedIdentifier(share<Identifier>(identifier), share<Sort>(sort));
}

// smt_literal.h
SmtPtr smt_newNumeralLiteral(long value) {
    return new NumeralLiteral(value);
}

SmtPtr smt_newDecimalLiteral(double value) {
    return new DecimalLiteral(value);
}

SmtPtr smt_newStringLiteral(char const* value) {
    return new StringLiteral(value);
}

// smt_logic.h
SmtPtr smt_newSmtLogic1(SmtPtr name) {
    return new SmtLogic(share<Symbol>(name));
}

SmtPtr smt_newSmtLogic2(SmtPtr name, SmtList attributes) {
    return new SmtLogic(share<Symbol>(name),
                        attributes->unwrap<Attribute>());
}

// smt_s_expr.h
SmtPtr smt_newCompSExpression(SmtList exprs) {
    return new CompSExpression(exprs->unwrap<ISExpression>());
}

// smt_script.h
SmtPtr smt_newSmtScript1() {
    return new SmtScript();
}

SmtPtr smt_newSmtScript2(SmtList cmds) {
    return new SmtScript(cmds->unwrap<Command>());
}

// smt_sort.h
SmtPtr smt_newSort1(SmtPtr identifier) {
    return new Sort(share<Identifier>(identifier));
}

SmtPtr smt_newSort2(SmtPtr identifier, SmtList params) {
    return new Sort(share<Identifier>(identifier),
                    params->unwrap<Sort>());
}

// smt_symbol_decl.h
SmtPtr smt_newSortSymbolDeclaration1(SmtPtr identifier, SmtPtr arity) {
    return new SortSymbolDeclaration(share<Identifier>(identifier),
                                     share<NumeralLiteral>(arity));
}

SmtPtr smt_newSortSymbolDeclaration1(SmtPtr identifier, SmtPtr arity, SmtList attributes) {
    return new SortSymbolDeclaration(share<Identifier>(identifier),
                                     share<NumeralLiteral>(arity),
                                     attributes->unwrap<Attribute>());
}

SmtPtr smt_newSpecConstFunDeclaration1(SmtPtr constant, SmtPtr sort) {
    return new SpecConstFunDeclaration(share<ISpecConstant>(constant), share<Sort>(sort));
}

SmtPtr smt_newSpecConstFunDeclaration2(SmtPtr constant, SmtPtr sort, SmtList attributes) {
    return new SpecConstFunDeclaration(share<ISpecConstant>(constant), share<Sort>(sort),
                                       attributes->unwrap<Attribute>());
}

SmtPtr smt_newMetaSpecConstFunDeclaration1(SmtPtr constant, SmtPtr sort) {
    return new MetaSpecConstFunDeclaration(share<MetaSpecConstant>(constant), share<Sort>(sort));
}

SmtPtr smt_newMetaSpecConstFunDeclaration2(SmtPtr constant, SmtPtr sort, SmtList attributes) {
    return new MetaSpecConstFunDeclaration(share<MetaSpecConstant>(constant), share<Sort>(sort),
                                           attributes->unwrap<Attribute>());
}

SmtPtr smt_newIdentifFunDeclaration1(SmtPtr identifier, SmtList signature) {
    return new IdentifFunDeclaration(share<Identifier>(identifier),
                                     signature->unwrap<Sort>());
}

SmtPtr smt_newIdentifFunDeclaration2(SmtPtr identifier, SmtList signature, SmtList attributes) {
    return new IdentifFunDeclaration(share<Identifier>(identifier),
                                     signature->unwrap<Sort>(),
                                     attributes->unwrap<Attribute>());
}

SmtPtr smt_newParamFunDeclaration1(SmtList params, SmtPtr identifier, SmtList signature) {
    return new ParamFunDeclaration(params->unwrap<Symbol>(),
                                   share<Identifier>(identifier),
                                   signature->unwrap<Sort>());
}

SmtPtr smt_newParamFunDeclaration2(SmtList params, SmtPtr identifier, SmtList signature, SmtList attributes) {
    return new ParamFunDeclaration(params->unwrap<Symbol>(),
                                   share<Identifier>(identifier),
                                   signature->unwrap<Sort>(),
                                   attributes->unwrap<Attribute>());
}

// smt_term.h
SmtPtr smt_newQualifiedTerm(SmtPtr identifier, SmtList terms) {
    return new QualifiedTerm(share<IQualIdentifier>(identifier),
                             terms->unwrap<ITerm>());
}

SmtPtr smt_newLetTerm(SmtList bindings, SmtPtr term) {
    return new LetTerm(bindings->unwrap<VarBinding>(),
                       share<ITerm>(term));
}

SmtPtr smt_newForallTerm(SmtList bindings, SmtPtr term) {
    return new ForallTerm(bindings->unwrap<SortedVariable>(),
                          share<ITerm>(term));
}

SmtPtr smt_newExistsTerm(SmtList bindings, SmtPtr term) {
    return new ExistsTerm(bindings->unwrap<SortedVariable>(),
                          share<ITerm>(term));
}

SmtPtr smt_newAnnotatedTerm(SmtPtr term, SmtList attrs) {
    return new AnnotatedTerm(share<ITerm>(term),
                             attrs->unwrap<Attribute>());
}

// smt_theory.h
SmtPtr smt_newSmtTheory1(SmtPtr name) {
    return new SmtTheory(share<Symbol>(name));
}

SmtPtr smt_newSmtTheory2(SmtPtr name, SmtList attributes) {
    return new SmtTheory(share<Symbol>(name),
                         attributes->unwrap<Attribute>());
}

// smt_var.h
SmtPtr smt_newSortedVariable(SmtPtr symbol, SmtPtr sort) {
    return new SortedVariable(share<Symbol>(symbol), share<Sort>(sort));
}

SmtPtr smt_newVarBinding(SmtPtr symbol, SmtPtr term) {
    return new VarBinding(share<Symbol>(symbol), share<ITerm>(term));
}
