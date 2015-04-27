#ifndef PARSE_SMTLIB_SMTLIB_GLUE_H
#define PARSE_SMTLIB_SMTLIB_GLUE_H

#ifdef __cplusplus
#include "../smt/ast/smt_abstract.h"
namespace smt {
    namespace ast {
        class SmtAstNode;
        class ParserInternalList;
    }
}
typedef class smt::ast::SmtAstNode *SmtPtr;
typedef class smt::ast::ParserInternalList *SmtList;
#else
typedef void *SmtPtr, *SmtList;
#endif

SmtList smt_listCreate();
void smt_listAdd(SmtList list, SmtPtr item);
void smt_listDelete(SmtList list);

// smt_attribute.h
SmtPtr smt_newAttribute1(SmtPtr keyword);
SmtPtr smt_newAttribute2(SmtPtr keyword, SmtPtr attr_value);

// smt_basic.h
SmtPtr smt_newKeyword(char const* value);
SmtPtr smt_newMetaSpecConstant(int value);
SmtPtr smt_newBooleanValue(bool value);
SmtPtr smt_newPropLiteral(SmtPtr symbol, bool negated);

// smt_command.h
SmtPtr smt_newAssertCommand(SmtPtr term);
SmtPtr smt_newCheckSatCommand();
SmtPtr smt_newCheckSatAssumCommand(SmtList assumptions);
SmtPtr smt_newDeclareConstCommand(SmtPtr symbol, SmtPtr sort);
SmtPtr smt_newDeclareFunCommand(SmtPtr symbol, SmtList params, SmtPtr sort);
SmtPtr smt_newDeclareSortCommand(SmtPtr symbol, SmtPtr arity);
SmtPtr smt_newDefineFunCommand(SmtPtr definition);
SmtPtr smt_newDefineFunRecCommand(SmtPtr definition);
SmtPtr smt_newDefineFunsRecCommand(SmtList declarations, SmtList bodies);
SmtPtr smt_newDefineSortCommand(SmtPtr symbol, SmtList params, SmtPtr sort);
SmtPtr smt_newEchoCommand(char*);
SmtPtr smt_newExitCommand();
SmtPtr smt_newGetAssertsCommand();
SmtPtr smt_newGetAssignsCommand();
SmtPtr smt_newGetInfoCommand(SmtPtr keyword);
SmtPtr smt_newGetModelCommand();
SmtPtr smt_newGetOptionCommand(SmtPtr keyword);
SmtPtr smt_newGetProofCommand();
SmtPtr smt_newGetUnsatAssumsCommand();
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
SmtPtr smt_newQualifiedIdentifier(SmtPtr identifier, SmtPtr sort);

// smt_literal.h
SmtPtr smt_newNumeralLiteral(long value);
SmtPtr smt_newDecimalLiteral(double value);
SmtPtr smt_newStringLiteral(char const* value);

// smt_logic.h
SmtPtr smt_newSmtLogic1(SmtPtr name);
SmtPtr smt_newSmtLogic2(SmtPtr name, SmtList attributes);

// smt_s_expr.h
SmtPtr smt_newCompSExpression(SmtList exprs);

// smt_script.h
SmtPtr smt_newSmtScript1();
SmtPtr smt_newSmtScript2(SmtList cmds);

// smt_sort.h
SmtPtr smt_newSort1(SmtPtr identifier);
SmtPtr smt_newSort2(SmtPtr identifier, SmtList params);

// smt_symbol_decl.h
SmtPtr smt_newSortSymbolDeclaration1(SmtPtr identifier, SmtPtr arity);
SmtPtr smt_newSortSymbolDeclaration1(SmtPtr identifier, SmtPtr arity, SmtList attributes);
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

#ifdef __cplusplus
extern "C" {
#endif


#ifdef __cplusplus
}; // extern "C"
#endif

#endif //PARSE_SMTLIB_SMTLIB_GLUE_H
