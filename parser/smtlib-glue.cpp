#include <memory>
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
                result.push_back(std::shared_ptr<T>(dynamic_cast<T>(v[i])));
            }
            v.clear();
            return result;
        };

        inline void add(SmtPtr item) {
            v.push_back(item);
        }
    };
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

SmtPtr smt_newMetaSpecConstant(); // fixme: type?

SmtPtr smt_newBooleanValue(bool value) {
    return new BooleanValue(value);
}

SmtPtr smt_newPropLiteral(SmtPtr symbol, bool negated) {
    return new PropLiteral(share<Symbol>(symbol), negated);
}

// smt_command.h
SmtPtr smt_newAssertCommand(SmtPtr term);
SmtPtr smt_newCheckSatCommand();
SmtPtr smt_newCheckSatAssumCommand(SmtList assumptions);
SmtPtr smt_newDeclareConstCommand(SmtPtr symbol, SmtPtr sort);
SmtPtr smt_newDeclareFunCommand(SmtPtr symbol, SmtList params, SmtPtr sort);
SmtPtr smt_newDeclareSortCommand(SmtPtr symbol, SmtPtr arity);
SmtPtr smt_newDefineFunCommand1(SmtPtr definition);
SmtPtr smt_newDefineFunCommand2(SmtPtr definition, SmtPtr body);
SmtPtr smt_newDefineFunCommand3(SmtPtr symbol, SmtList params, SmtPtr sort, SmtPtr body);
SmtPtr smt_newDefineFunRecCommand1(SmtPtr definition);
SmtPtr smt_newDefineFunRecCommand2(SmtPtr definition, SmtPtr body);
SmtPtr smt_newDefineFunRecCommand3(SmtPtr symbol, SmtList params, SmtPtr sort, SmtPtr body);
SmtPtr smt_newDefineFunsRecCommand(SmtList definitions);
SmtPtr smt_newDefineSortCommand(SmtPtr symbol, SmtList params, SmtPtr sort);
SmtPtr smt_newEchoCommand(char*);
SmtPtr smt_newExitCommand();
SmtPtr smt_newGetAssertsCommand();
SmtPtr smt_newGetAssignsCommand();
SmtPtr smt_newGetInfoCommand(SmtPtr keyword);
SmtPtr smt_newGetOptionCommand(SmtPtr keyword);
SmtPtr smt_newGetProofCommand();
SmtPtr smt_newGetUnsatCoreCommand();
SmtPtr smt_newGetValueCommand(SmtList terms);
SmtPtr smt_newPopCommand(SmtPtr numeral);
SmtPtr smt_newPushCommand(SmtPtr numeral);
SmtPtr smt_newResetCommand();
SmtPtr smt_newResetAssertsCommand();
SmtPtr smt_newSetInfoCommand(SmtPtr info);
SmtPtr smt_newSetLogicCommand(SmtPtr logic);
SmtPtr smt_newSetOptionCommand(SmtPtr option);

// smt_fun.h
SmtPtr smt_newFunctionDeclaration(SmtPtr symbol, SmtList params, SmtPtr sort);
SmtPtr smt_newFunctionDefinition(SmtPtr signature, SmtPtr body);

// smt_identifier.h
SmtPtr smt_newIdentifier1(SmtPtr symbol);
SmtPtr smt_newIdentifier2(SmtPtr symbol, SmtList indices);
SmtPtr smt_newQualifiedIdentifier(SmtPtr identifier, SmtList sort);

// smt_literal.h
SmtPtr smt_newNumeralLiteral(long value);
SmtPtr smt_newDecimalLiteral(double value);
SmtPtr smt_newStringLiteral(char const* value);

// smt_logic.h
SmtPtr smt_newSmtLogic(SmtPtr name);

// smt_s_expr.h
SmtPtr smt_newCompSExpression(SmtList exprs);

// smt_script.h
SmtPtr smt_newSmtScript1();
SmtPtr smt_newSmtScript2(SmtList cmds);

// smt_sort.h
SmtPtr smt_newSort1(SmtPtr identifier);
SmtPtr smt_newSort2(SmtPtr identifier, SmtList params);

// smt_symbol_decl.h
SmtPtr smt_newSortSymbolDeclaration1(SmtPtr identifier, long arity);
SmtPtr smt_newSortSymbolDeclaration1(SmtPtr identifier, long arity, SmtList attributes);
SmtPtr smt_newSpecConstFunDeclaration1(SmtPtr constant, SmtPtr sort);
SmtPtr smt_newSpecConstFunDeclaration2(SmtPtr constant, SmtPtr sort, SmtList attributes);
SmtPtr smt_newMetaSpecConstFunDeclaration1(SmtPtr constant, SmtPtr sort);
SmtPtr smt_newMetaSpecConstFunDeclaration2(SmtPtr constant, SmtPtr sort, SmtList attributes);
SmtPtr smt_newIdentifFunDeclaration1(SmtPtr identifier, SmtList signature);
SmtPtr smt_newIdentifFunDeclaration2(SmtPtr identifier, SmtList signature, SmtList attributes);
SmtPtr smt_newParamFunDeclaration1(SmtList params, SmtPtr identifier, SmtList signature);
SmtPtr smt_newParamFunDeclaration2(SmtList params, SmtPtr identifier, SmtList signature, SmtList attributes);

// smt_term.h
SmtPtr smt_newQualifiedTerm(SmtPtr identifier, SmtList terms);
SmtPtr smt_newLetTerm(SmtList bindings, SmtPtr term);
SmtPtr smt_newForallTerm(SmtList bindings, SmtPtr term);
SmtPtr smt_newExistsTerm(SmtList bindings, SmtPtr term);
SmtPtr smt_newAnnotatedTerm(SmtPtr term, SmtList attrs);

// smt_theory.h
SmtPtr smt_newSmtTheory1(SmtPtr name);
SmtPtr smt_newSmtTheory2(SmtPtr name, SmtList attributes);

// smt_var.h
SmtPtr smt_newSortedVariable(SmtPtr symbol, SmtPtr sort);
SmtPtr smt_newVarBinding(SmtPtr symbol, SmtPtr term);
