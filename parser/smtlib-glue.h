#ifndef PARSE_SMTLIB_SMTLIB_GLUE_H
#define PARSE_SMTLIB_SMTLIB_GLUE_H

#ifdef __cplusplus
#include "../smtlib/ast/smt_abstract.h"
namespace smtlib {
    namespace ast {
        class AstNode;
        class ParserInternalList;
    }
    class Parser;
}
typedef class smtlib::ast::AstNode *SmtPtr;
typedef class smtlib::ast::ParserInternalList *SmtList;
typedef class smtlib::Parser *SmtPrsr;
#else
typedef void *SmtPtr, *SmtList, *SmtPrsr;
#endif

#ifdef __cplusplus
extern "C" {
#endif

int yylex (void);
int yyparse(SmtPrsr);

void smt_setAst(SmtPrsr parser, SmtPtr ast);

SmtList smt_listCreate();
void smt_listAdd(SmtList list, SmtPtr item);
void smt_listDelete(SmtList list);

void smt_print(SmtPtr ptr);

int smt_bool_value(SmtPtr ptr);

// smt_attribute.h
SmtPtr smt_newAttribute1(SmtPtr keyword);
SmtPtr smt_newAttribute2(SmtPtr keyword, SmtPtr attr_value);
SmtPtr smt_newCompoundAttributeValue(SmtList values);

// smt_basic.h
SmtPtr smt_newSymbol(char const* value);
SmtPtr smt_newKeyword(char const* value);
SmtPtr smt_newMetaSpecConstant(int value);
SmtPtr smt_newBooleanValue(int value);
SmtPtr smt_newPropLiteral(SmtPtr symbol, int negated);

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
SmtPtr smt_newEchoCommand(SmtPtr);
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
SmtPtr smt_newNumeralLiteral(long value, unsigned int base);
SmtPtr smt_newDecimalLiteral(double value);
SmtPtr smt_newStringLiteral(char const* value);

// smt_logic.h
SmtPtr smt_newLogic(SmtPtr name, SmtList attributes);

// smt_s_expr.h
SmtPtr smt_newCompSExpression(SmtList exprs);

// smt_script.h
SmtPtr smt_newSmtScript(SmtList cmds);

// smt_sort.h
SmtPtr smt_newSort1(SmtPtr identifier);
SmtPtr smt_newSort2(SmtPtr identifier, SmtList params);

// smt_symbol_decl.h
SmtPtr smt_newSortSymbolDeclaration(SmtPtr identifier, SmtPtr arity, SmtList attributes);
SmtPtr smt_newSpecConstFunDeclaration(SmtPtr constant, SmtPtr sort, SmtList attributes);
SmtPtr smt_newMetaSpecConstFunDeclaration(SmtPtr constant, SmtPtr sort, SmtList attributes);
SmtPtr smt_newIdentifFunDeclaration(SmtPtr identifier, SmtList signature, SmtList attributes);
SmtPtr smt_newParamFunDeclaration(SmtList params, SmtPtr identifier, SmtList signature, SmtList attributes);

// smt_term.h
SmtPtr smt_newQualifiedTerm(SmtPtr identifier, SmtList terms);
SmtPtr smt_newLetTerm(SmtList bindings, SmtPtr term);
SmtPtr smt_newForallTerm(SmtList bindings, SmtPtr term);
SmtPtr smt_newExistsTerm(SmtList bindings, SmtPtr term);
SmtPtr smt_newAnnotatedTerm(SmtPtr term, SmtList attrs);

// smt_theory.h
SmtPtr smt_newTheory(SmtPtr name, SmtList attributes);

// smt_var.h
SmtPtr smt_newSortedVariable(SmtPtr symbol, SmtPtr sort);
SmtPtr smt_newVarBinding(SmtPtr symbol, SmtPtr term);

#ifdef __cplusplus
}; // extern "C"
#endif

#endif //PARSE_SMTLIB_SMTLIB_GLUE_H
