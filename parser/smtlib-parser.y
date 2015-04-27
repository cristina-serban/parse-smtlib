%{
#include <stdio.h>
#include "smtlib-glue.h"
%}

%token KW_AS KW_LET KW_FORALL KW_EXISTS KW_PAR
%token NUMERAL DECIMAL HEXADECIMAL BINARY BOOL_VALUE NOT
%token CMD_ASSERT CMD_CHK_SAT CMD_CHK_SAT_ASSUM CMD_DECL_CONST CMD_DECL_FUN CMD_DECL_SORT
%token CMD_DEF_FUN CMD_DEF_FUN_REC CMD_DEF_FUNS_REC CMD_DEF_SORT CMD_ECHO CMD_EXIT
%token CMD_GET_ASSERTS CMD_GET_ASSIGNS CMD_GET_INFO CMD_GET_MODEL CMD_GET_OPT CMD_GET_PROOF
%token CMD_GET_UNSAT_ASSUMS CMD_GET_UNSAT_CORE CMD_GET_VALUE CMD_POP CMD_PUSH
%token CMD_RESET CMD_RESET_ASSERTS CMD_SET_INFO CMD_SET_LOGIC CMD_SET_OPT
%token META_SPEC_DECIMAL META_SPEC_NUMERAL META_SPEC_STRING
%token KEYWORD STRING SYMBOL THEORY LOGIC
%token OPT_DIAGN_OUTPUT_CHANNEL OPT_EXPAND_DEFS OPT_GLOBAL_DECLS OPT_INTERACT_MODE
%token OPT_PRINT_SUCCESS OPT_PROD_ASSERTS OPT_PROD_ASSIGNS OPT_PROD_MODELS
%token OPT_PROD_PROOFS OPT_PROD_UNSAT_ASSUMS OPT_PROD_UNSAT_CORES OPT_RAND_SEED
%token OPT_REG_OUTPUT_CHANNEL OPT_REPROD_RES_LIMIT OPT_VERBOSITY
%token ATTR_SORTS ATTR_FUNS ATTR_SORTS_DESC ATTR_FUNS_DESC ATTR_DEF ATTR_VALUES 
%token ATTR_NOTES ATTR_THEORIES ATTR_LANG ATTR_EXTS

%start smt_file

%%

smt_file:
	script			{ $$ = $1; }
|
	theory_decl		{ $$ = $1; }
|
	logic 			{ $$ = $1; }
;

script:
	command_plus	{ $$ = smt_newSmtScript2($1); }
;

command_plus:
	command 				
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	command_plus command 	
		{ smt_listAdd($1, $2); $$ = $1; }
;

command:
	'(' CMD_ASSERT term ')'		
		{ $$ = smt_newAssertCommand($3); }
|
	'(' CMD_CHK_SAT ')'			
		{ $$ = smt_newCheckSatCommand(); }
|
	'(' CMD_CHK_SAT_ASSUM '(' prop_literal_star ')' ')'		
		{ $$ = smt_newCheckSatAssumCommand(); }
|
	'(' CMD_DECL_CONST SYMBOL sort ')'						
		{ $$ = smt_newDeclareConstCommand($3, $4); }
|
	'(' CMD_DECL_FUN SYMBOL '(' sort_plus ')' sort ')'
		{ $$ = smt_newDeclareFunCommand($3, $5, $7); }
|
	'(' CMD_DECL_SORT SYMBOL NUMERAL ')'
		{ $$ = smt_newDeclareSortCommand($3, $4); }
|
	'(' CMD_DEF_FUNS_REC '(' fun_decl_plus ')'  '(' term_plus ')' ')'
		{ $$ = smt_newDefineFunsRecCommand($4, $7); }
|	
	'(' CMD_DEF_FUN_REC fun_def ')'
		{ $$ = smt_newDefineFunRecCommand($3); }
|
	'(' CMD_DEF_FUN SYMBOL fun_def ')'
		{ $$ = smt_newDefineFunRecCommand($3); }
|
	'(' CMD_DEF_SORT SYMBOL '(' symbol_star ')' sort ')'
		{ $$ = smt_newDefineSortCommand($3, $5, $7); }
|
	'(' CMD_ECHO STRING ')'
		{ $$ = smt_newEchoCommand($2); }
|
	'(' CMD_EXIT ')'
		{ $$ = smt_newExitCommand(); }
|
	'(' CMD_GET_ASSERTS ')'
		{ $$ = smt_newGetAssertsCommand(); }
|
	'(' CMD_GET_ASSIGNS ')'
		{ $$ = smt_newGetAssignsCommand(); }
|
	'(' CMD_GET_INFO info_flag ')' 
		{ $$ = smt_newGetInfoCommand($3); }
|
	'(' CMD_GET_MODEL ')'
		{ $$ = smt_newGetModelCommand(); }
|
	'(' CMD_GET_OPT KEYWORD ')'
		{ $$ = smt_newGetOptionCommand($3); }
|
	'(' CMD_GET_PROOF ')'
		{ $$ = smt_newGetProofCommand(); }
|
	'(' CMD_GET_UNSAT_ASSUMS ')'
		{ $$ = smt_newGetModelCommand(); }
|
	'(' CMD_GET_UNSAT_CORE ')'
		{ $$ = smt_newGetUnsatCoreCommand(); }
|
	'(' CMD_GET_VALUE term_plus ')'
		{ $$ = smt_newGetValueCommand($3); }
|
	'(' CMD_POP NUMERAL ')'
		{ $$ = smt_newPopCommand($3); }
|
	'(' CMD_PUSH NUMERAL ')'
		{ $$ = smt_newPushCommand($3); }
|
	'(' CMD_RESET_ASSERTS ')'
		{ $$ = smt_newResetAssertsCommand(); }
|
	'(' CMD_RESET ')'
		{ $$ = smt_newResetCommand(); }
|
	'(' CMD_SET_INFO attribute ')'
		{ $$ = smt_newSetInfoCommand($3); }
|
	'(' CMD_SET_LOGIC SYMBOL ')'
		{ $$ = smt_newSetLogicCommand($3); }
|
	'(' CMD_SET_OPT option ')'
		{ $$ = smt_newSetOptionCommand($3); }
;

term:
	spec_const 			{ $$ = $1; }
|
	qual_identifier		{ $$ = $1; }
|
	'(' qual_identifier term_plus ')' 
		{ $$ = smt_newQualifiedTerm($2, $3); }
|
	'(' KW_LET '(' var_binding_plus ')' term ')'
		{ $$ = smt_newLetTerm($4, $6); }
|
	'(' KW_FORALL '(' sorted_var_plus ')' term ')'
		{ $$ = smt_newForallTerm($4, $6); }
|
	'(' KW_EXISTS '(' sorted_var_plus ')' term ')'
		{ $$ = smt_newExistsTerm($4, $6); }
|
	'(' '!' term attribute_plus ')'
		{ $$ = smt_newAnnotatedTerm($3, $4); }
;

term_plus:
	term 				
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	term_plus term 		
		{ smt_listAdd($1, $2); $$ = $1; }
;

spec_const:
	NUMERAL 		{ $$ = $1; }
|
	DECIMAL 		{ $$ = $1; }
|
	HEXADECIMAL 	{ $$ = $1; }
|
	BINARY 			{ $$ = $1; }
|
	STRING 			{ $$ = $1; }
;

qual_identifier:
	identifier 		{ $$ = $1; }
|
	'(' KW_AS identifier sort ')'
		{ $$ = smt_newQualifiedIdentifier($3, $4); }
;

identifier:
	SYMBOL 			
		{ $$ = smt_newIdentifier1($1); }
|
	'(' '_' SYMBOL index_plus ')'
		{ $$ = smt_newIdentifier2($3, $4); }
;

index:
	NUMERAL 	{ $$ = $1; }
|
	SYMBOL 		{ $$ = $1; }
;

index_plus:
	index 				
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	index_plus index 	
		{ smt_listAdd($1, $2); $$ = $1; }
;

sort:
	identifier
|
	'(' identifier sort_plus ')'
;

sort_plus:
	sort
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	sort_plus sort
		{ smt_listAdd($1, $2); $$ = $1; }
;

var_binding:
	'(' SYMBOL term ')'
;

var_binding_plus:
	var_binding
|
	var_binding_plus var_binding
;

sorted_var:
	'(' SYMBOL sort ')'
;

sorted_var_plus:
	sorted_var
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	sorted_var_plus sorted_var
		{ smt_listAdd($1, $2); $$ = $1; }
;

attribute:
	KEYWORD
|
	KEYWORD attr_value
;

attribute_star:
	/* empty */
		{ $$ = smt_listCreate(); }
|
	attribute_star attribute
		{ smt_listAdd($1, $2); $$ = $1; }
;

attribute_plus:
	attribute
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	attribute_plus attribute
		{ smt_listAdd($1, $2); $$ = $1; }
;

attr_value:
	spec_const
|
	SYMBOL
|
	'(' s_exp_plus ')'
;

s_exp:
	spec_const
|
	SYMBOL
|
	KEYWORD
|
	'(' s_exp_plus ')'
;

s_exp_plus :
	s_exp 
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	s_exp_plus s_exp
		{ smt_listAdd($1, $2); $$ = $1; }
;

prop_literal:
	SYMBOL 
|
	'(' NOT SYMBOL ')'
;

prop_literal_star:
	/* empty */
		{ $$ = smt_listCreate(); }

|
	prop_literal_star prop_literal
		{ smt_listAdd($1, $2); $$ = $1; }
;

fun_decl:
	'(' SYMBOL '(' sorted_var_plus ')' sort ')'
;

fun_decl_plus:
	fun_decl
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	fun_decl_plus fun_decl
		{ smt_listAdd($1, $2); $$ = $1; }
;

fun_def:
	SYMBOL '(' sorted_var_plus ')' sort term
;

symbol_star:
	/* empty */
		{ $$ = smt_listCreate(); }
|
	symbol_star SYMBOL
		{ smt_listAdd($1, $2); $$ = $1; }
;

symbol_plus:
	SYMBOL
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	symbol_plus SYMBOL
		{ smt_listAdd($1, $2); $$ = $1; }
;

info_flag:
	KEYWORD { $$ = $1; }
;

option:
	OPT_DIAGN_OUTPUT_CHANNEL STRING
		{ $$ = smt_newAttribute2($1, $2); }
|
	OPT_EXPAND_DEFS BOOL_VALUE
		{ $$ = smt_newAttribute2($1, $2); }
| 
	OPT_GLOBAL_DECLS BOOL_VALUE
		{ $$ = smt_newAttribute2($1, $2); }
| 
	OPT_INTERACT_MODE BOOL_VALUE
		{ $$ = smt_newAttribute2($1, $2); }
| 
	OPT_PRINT_SUCCESS BOOL_VALUE
		{ $$ = smt_newAttribute2($1, $2); }
| 
	OPT_PROD_ASSERTS BOOL_VALUE
		{ $$ = smt_newAttribute2($1, $2); }
|
	OPT_PROD_ASSIGNS BOOL_VALUE
		{ $$ = smt_newAttribute2($1, $2); }
|
	OPT_PROD_MODELS BOOL_VALUE
		{ $$ = smt_newAttribute2($1, $2); }
|
	OPT_PROD_PROOFS BOOL_VALUE
		{ $$ = smt_newAttribute2($1, $2); }
|
	OPT_PROD_UNSAT_ASSUMS BOOL_VALUE
		{ $$ = smt_newAttribute2($1, $2); }
|
	OPT_PROD_UNSAT_CORES BOOL_VALUE
		{ $$ = smt_newAttribute2($1, $2); }
|
	OPT_RAND_SEED NUMERAL
		{ $$ = smt_newAttribute2($1, $2); }
|
	OPT_REG_OUTPUT_CHANNEL STRING
		{ $$ = smt_newAttribute2($1, $2); }
|
	OPT_REPROD_RES_LIMIT NUMERAL
		{ $$ = smt_newAttribute2($1, $2); }
|
	OPT_VERBOSITY NUMERAL
		{ $$ = smt_newAttribute2($1, $2); }
|
	attribute 	{ $$ = $1; }
;

theory_decl:
	'(' THEORY SYMBOL theory_attr_plus ')'
		{ $$ = smt_newSmtLogic($3, $4); }
;

theory_attr:
	ATTR_SORTS '(' sort_symbol_decl_plus ')'
		{ $$ = smt_newAttribute2($1, $3); }
|
	ATTR_FUNS '(' par_fun_symbol_decl_plus ')'
		{ $$ = smt_newAttribute2($1, $3); }
|
	ATTR_SORTS_DESC STRING
		{ $$ = smt_newAttribute2($1, $2); }
|
	ATTR_FUNS_DESC STRING
		{ $$ = smt_newAttribute2($1, $2); }
|	
	ATTR_DEF STRING
		{ $$ = smt_newAttribute2($1, $2); }
|
	ATTR_VALUES STRING
		{ $$ = smt_newAttribute2($1, $2); }
|
	ATTR_NOTES STRING
		{ $$ = smt_newAttribute2($1, $2); }
|	
	attribute 	{ $$ = $1; }
;

theory_attr_plus:
	theory_attr
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	theory_attr_plus theory_attr
		{ smt_listAdd($1, $2); $$ = $1; }
;

sort_symbol_decl:
	'(' identifier NUMERAL attribute_star ')'
;

sort_symbol_decl_plus:
	sort_symbol_decl
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	sort_symbol_decl_plus sort_symbol_decl
		{ smt_listAdd($1, $2); $$ = $1; }
;

par_fun_symbol_decl:
	fun_symbol_decl
|
	'(' KW_PAR '(' symbol_plus ')' '(' identifier sort_plus attribute_star ')' ')'
;

par_fun_symbol_decl_plus:
	par_fun_symbol_decl
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	par_fun_symbol_decl_plus par_fun_symbol_decl
		{ smt_listAdd($1, $2); $$ = $1; }
;

fun_symbol_decl:
	'(' spec_const sort attribute_star ')'
|
	'(' meta_spec_const sort attribute_star ')'
|
	'(' identifier sort_plus attribute_star ')'
;

meta_spec_const:
	META_SPEC_NUMERAL
		{ $$ =  smt_newMetaSpecConstant(0); }
|
	META_SPEC_DECIMAL
		{ $$ =  smt_newMetaSpecConstant(1); }
|
	META_SPEC_STRING
		{ $$ =  smt_newMetaSpecConstant(2); }
;

logic:
	'(' LOGIC SYMBOL logic_attr_plus ')'
		{ $$ = smt_newSmtLogic($3, $4); }
;

logic_attr:
	ATTR_THEORIES '(' symbol_plus ')'
		{ $$ = smt_newAttribute2($1, smt_newCompSExpression($2)); }
|
	ATTR_LANG STRING
		{ $$ = smt_newAttribute2($1, $2); }
|
	ATTR_EXTS STRING
		{ $$ = smt_newAttribute2($1, $2); }
|
	ATTR_VALUES STRING
		{ $$ = smt_newAttribute2($1, $2); }
|
	ATTR_NOTES STRING
		{ $$ = smt_newAttribute2($1, $2); }
|
	attribute 	{ $$ = $1; }
;

logic_attr_plus:
	logic_attr
		{ $$ = smt_listCreate(); smt_listAdd($$, $1); }
|
	logic_attr_plus logic_attr
		{ smt_listAdd($1, $2); $$ = $1; }
;

%%

int yyerror(char *s) {
	printf("yyerror: %s\n", s);
}

int main() {
	yyparse();
}