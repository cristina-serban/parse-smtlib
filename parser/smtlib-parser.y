%{
#include <stdio.h>
%}

%token KW_AS KW_LET KW_FORALL KW_EXISTS KW_PAR
%token NUMERAL DECIMAL HEXADECIMAL BINARY BOOL_VALUE NOT
%token CMD_ASSERT CMD_CHK_SAT CMD_CHK_SAT_ASSUM CMD_DECL_CONST CMD_DECL_FUN CMD_DECL_SORT
%token CMD_DEF_FUN CMD_DEF_FUN_REC CMD_DEF_FUNS_REC CMD_DEF_SORT CMD_ECHO CMD_EXIT
%token CMD_GET_ASSERTS CMD_GET_ASSIGNS CMD_GET_INFO CMD_GET_MODEL CMD_GET_OPT CMD_GET_PROOF
%token CMD_GET_UNSAT_ASSUM CMD_GET_UNSAT_CORE CMD_GET_VALUE CMD_POP CMD_PUSH
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
	script
|
	theory_decl
|
	logic
;

script:
	command_plus
;

command_plus:
	command
|
	command_plus command
;

command:
	'(' CMD_ASSERT term ')'
|
	'(' CMD_CHK_SAT ')'
|
	'(' CMD_CHK_SAT_ASSUM '(' prop_literal_star ')' ')'
|
	'(' CMD_DECL_CONST SYMBOL sort ')'
|
	'(' CMD_DECL_FUN SYMBOL '(' sort_plus ')' sort ')'
|
	'(' CMD_DECL_SORT SYMBOL NUMERAL ')'
|
	'(' CMD_DEF_FUNS_REC '(' fun_decl_plus ')'  '(' term_plus ')' ')'
|	
	'(' CMD_DEF_FUN_REC fun_def ')'
|
	'(' CMD_DEF_FUN SYMBOL fun_def ')'
|
	'(' CMD_DEF_SORT SYMBOL '(' symbol_star ')' sort_plus ')'
|
	'(' CMD_ECHO STRING ')'
|
	'(' CMD_EXIT ')'
|
	'(' CMD_GET_ASSERTS ')'
|
	'(' CMD_GET_ASSIGNS ')'
|
	'(' CMD_GET_INFO info_flag ')'
|
	'(' CMD_GET_MODEL ')'
|
	'(' CMD_GET_OPT KEYWORD ')'
|
	'(' CMD_GET_PROOF ')'
|
	'(' CMD_GET_UNSAT_ASSUM ')'
|
	'(' CMD_GET_UNSAT_CORE ')'
|
	'(' CMD_GET_VALUE term_plus ')'
|
	'(' CMD_POP NUMERAL ')'
|
	'(' CMD_PUSH NUMERAL ')'
|
	'(' CMD_RESET_ASSERTS ')'
|
	'(' CMD_RESET ')'
|
	'(' CMD_SET_INFO attribute ')'
|
	'(' CMD_SET_LOGIC SYMBOL ')'
|
	'(' CMD_SET_OPT option ')'
;

term:
	spec_const
|
	qual_identifier
|
	'(' qual_identifier term_plus ')'
|
	'(' KW_LET '(' var_binding_plus ')' term ')'
|
	'(' KW_FORALL '(' sorted_var_plus ')' term ')'
|
	'(' KW_EXISTS '(' sorted_var_plus ')' term ')'
|
	'(' '!' term attribute_plus ')'
;

term_plus:
	term
|
	term_plus term
;

spec_const:
	NUMERAL
|
	DECIMAL
|
	HEXADECIMAL
|
	BINARY
|
	STRING
;

qual_identifier:
	identifier
|
	'(' KW_AS identifier sort ')'
;

identifier:
	SYMBOL
|
	'(' '_' SYMBOL index_plus ')'
;

index:
	NUMERAL
|
	SYMBOL
;

index_plus:
	index
|
	index_plus index
;

sort:
	identifier
|
	'(' identifier sort_plus ')'
;

sort_plus:
	sort
|
	sort_plus sort
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
|
	sorted_var_plus sorted_var
;

attribute:
	KEYWORD
|
	KEYWORD attr_value
;

attribute_star:
	/* empty */
|
	attribute_star attribute
;

attribute_plus:
	attribute
|
	attribute_plus attribute
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
|
	s_exp_plus s_exp
;

prop_literal:
	SYMBOL 
|
	'(' NOT SYMBOL ')'
;

prop_literal_star:
	/* empty */
|
	prop_literal_star prop_literal
;

fun_decl:
	'(' SYMBOL '(' sorted_var_plus ')' sort ')'
;

fun_decl_plus:
	fun_decl
|
	fun_decl_plus fun_decl
;

fun_def:
	SYMBOL '(' sorted_var_plus ')' sort term
;

symbol_star:
	/* empty */
|
	symbol_star SYMBOL
;

symbol_plus:
	SYMBOL
|
	symbol_plus SYMBOL
;

info_flag:
	KEYWORD
;

option:
	OPT_DIAGN_OUTPUT_CHANNEL STRING
|
	OPT_EXPAND_DEFS BOOL_VALUE
| 
	OPT_GLOBAL_DECLS BOOL_VALUE
| 
	OPT_INTERACT_MODE BOOL_VALUE
| 
	OPT_PRINT_SUCCESS BOOL_VALUE
| 
	OPT_PROD_ASSERTS BOOL_VALUE
|
	OPT_PROD_ASSIGNS BOOL_VALUE
|
	OPT_PROD_MODELS BOOL_VALUE
|
	OPT_PROD_PROOFS BOOL_VALUE
|
	OPT_PROD_UNSAT_ASSUMS BOOL_VALUE
|
	OPT_PROD_UNSAT_CORES BOOL_VALUE
|
	OPT_RAND_SEED NUMERAL
|
	OPT_REG_OUTPUT_CHANNEL STRING
|
	OPT_REPROD_RES_LIMIT NUMERAL
|
	OPT_VERBOSITY NUMERAL
|
	attribute
;

theory_decl:
	'(' THEORY SYMBOL theory_attr_plus ')'
;

theory_attr:
	ATTR_SORTS '(' sort_symbol_decl_plus ')'
|
	ATTR_FUNS '(' par_fun_symbol_decl_plus ')'
|
	ATTR_SORTS_DESC STRING
|
	ATTR_FUNS_DESC STRING
|	
	ATTR_DEF STRING
|
	ATTR_VALUES STRING
|
	ATTR_NOTES STRING
|	
	attribute
;

theory_attr_plus:
	theory_attr
|
	theory_attr_plus theory_attr
;

sort_symbol_decl:
	'(' identifier NUMERAL attribute_star ')'
;

sort_symbol_decl_plus:
	sort_symbol_decl
|
	sort_symbol_decl_plus sort_symbol_decl;

par_fun_symbol_decl:
	fun_symbol_decl
|
	'(' KW_PAR '(' symbol_plus ')' '(' identifier sort_plus attribute_star ')' ')'
;

par_fun_symbol_decl_plus:
	par_fun_symbol_decl
|
	par_fun_symbol_decl_plus par_fun_symbol_decl
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
|
	META_SPEC_DECIMAL
|
	META_SPEC_STRING
;

logic:
	'(' LOGIC SYMBOL logic_attr_plus ')'
;

logic_attr:
	ATTR_THEORIES '(' symbol_plus ')'
|
	ATTR_LANG STRING
|
	ATTR_EXTS STRING
|
	ATTR_VALUES STRING
|
	ATTR_NOTES STRING
|
	attribute
;

logic_attr_plus:
	logic_attr
|
	logic_attr_plus logic_attr
;

%%

int yyerror(char *s) {
	printf("yyerror: %s\n", s);
}

int main() {
	yyparse();
}