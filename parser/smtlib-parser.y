%{
#include <stdio.h>
#include "smtlib-glue.h"

int yylex(void);
int yyerror(const char *);
%}

%union
{
	SmtPtr ptr;
	SmtList list;
};

%token KW_AS KW_LET KW_FORALL KW_EXISTS KW_PAR NOT

%token <ptr> NUMERAL DECIMAL HEXADECIMAL BINARY

%token CMD_ASSERT CMD_CHK_SAT CMD_CHK_SAT_ASSUM CMD_DECL_CONST CMD_DECL_FUN CMD_DECL_SORT
%token CMD_DEF_FUN CMD_DEF_FUN_REC CMD_DEF_FUNS_REC CMD_DEF_SORT CMD_ECHO CMD_EXIT
%token CMD_GET_ASSERTS CMD_GET_ASSIGNS CMD_GET_INFO CMD_GET_MODEL CMD_GET_OPT CMD_GET_PROOF
%token CMD_GET_UNSAT_ASSUMS CMD_GET_UNSAT_CORE CMD_GET_VALUE CMD_POP CMD_PUSH
%token CMD_RESET CMD_RESET_ASSERTS CMD_SET_INFO CMD_SET_LOGIC CMD_SET_OPT

%token <ptr> META_SPEC_DECIMAL META_SPEC_NUMERAL META_SPEC_STRING
%token <ptr> KEYWORD STRING SYMBOL THEORY LOGIC

%token <ptr> ATTR_SORTS ATTR_FUNS ATTR_THEORIES

%type <ptr> smt_file script command term spec_const qual_identifier identifier index
%type <ptr> sort var_binding sorted_var attribute attr_value s_exp prop_literal
%type <ptr> fun_decl fun_def info_flag option theory_decl theory_attr sort_symbol_decl
%type <ptr> par_fun_symbol_decl fun_symbol_decl meta_spec_const logic logic_attr symbol

%type <list> command_plus term_plus index_plus sort_plus var_binding_plus sorted_var_plus
%type <list> attribute_star attribute_plus s_exp_plus prop_literal_star fun_decl_plus
%type <list> symbol_star symbol_plus theory_attr_plus sort_symbol_decl_plus
%type <list> par_fun_symbol_decl_plus logic_attr_plus sort_star sorted_var_star

%start smt_file

%%

smt_file:
	script			{ $$ = $1; smt_print($1); }
|
	theory_decl		{ $$ = $1; smt_print($1); }
|
	logic 			{ $$ = $1; smt_print($1); }
;

script:
	command_plus	{ $$ = smt_newSmtScript($1); }
;

command_plus:
	command 				
		{ 	
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	command_plus command 	
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

command:
	'(' CMD_ASSERT term ')'		
		{ $$ = smt_newAssertCommand($3); }
|
	'(' CMD_CHK_SAT ')'			
		{ $$ = smt_newCheckSatCommand(); }
|
	'(' CMD_CHK_SAT_ASSUM '(' prop_literal_star ')' ')'		
		{ $$ = smt_newCheckSatAssumCommand($4); }
|
	'(' CMD_DECL_CONST symbol sort ')'						
		{ $$ = smt_newDeclareConstCommand($3, $4); }
|
	'(' CMD_DECL_FUN symbol '(' sort_star ')' sort ')'
		{ $$ = smt_newDeclareFunCommand($3, $5, $7); }
|
	'(' CMD_DECL_SORT symbol NUMERAL ')'
		{ $$ = smt_newDeclareSortCommand($3, $4); }
|
	'(' CMD_DEF_FUNS_REC '(' fun_decl_plus ')'  '(' term_plus ')' ')'
		{ $$ = smt_newDefineFunsRecCommand($4, $7); }
|	
	'(' CMD_DEF_FUN_REC fun_def ')'
		{ $$ = smt_newDefineFunRecCommand($3); }
|
	'(' CMD_DEF_FUN fun_def ')'
		{ $$ = smt_newDefineFunCommand($3); }
|
	'(' CMD_DEF_SORT symbol '(' symbol_star ')' sort ')'
		{ $$ = smt_newDefineSortCommand($3, $5, $7); }
|
	'(' CMD_ECHO STRING ')'
		{ $$ = smt_newEchoCommand($3); }
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
	'(' CMD_SET_LOGIC symbol ')'
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
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	term_plus term 		
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
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

symbol:
	SYMBOL
		{ $$ = $1; }
|
	NOT
		{ $$ = smt_newSymbol("not"); }
;

qual_identifier:
	identifier 		{ $$ = $1; }
|
	'(' KW_AS identifier sort ')'
		{ $$ = smt_newQualifiedIdentifier($3, $4); }
;

identifier:
	symbol 			
		{ $$ = smt_newIdentifier1($1); }
|
	'(' '_' symbol index_plus ')'
		{ $$ = smt_newIdentifier2($3, $4); }
;

index:
	NUMERAL 	{ $$ = $1; }
|
	symbol 		{ $$ = $1; }
;

index_plus:
	index 				
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	index_plus index 	
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

sort:
	identifier 	
		{ $$ = smt_newSort1($1); }
|
	'(' identifier sort_plus ')'
		{ $$ = smt_newSort2($2, $3); }
;

sort_plus:
	sort
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	sort_plus sort
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

sort_star:
	/* empty */
		{ $$ = smt_listCreate(); }
|
	sort_star sort
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

var_binding:
	'(' symbol term ')'
		{ $$ = smt_newVarBinding($2, $3); }
;

var_binding_plus:
	var_binding
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	var_binding_plus var_binding
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

sorted_var:
	'(' symbol sort ')'
		{ $$ = smt_newSortedVariable($2, $3); }
;

sorted_var_plus:
	sorted_var
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	sorted_var_plus sorted_var
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

sorted_var_star:
	/* empty */
		{ $$ = smt_listCreate(); }
|
	sorted_var_star sorted_var
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

attribute:
	KEYWORD
		{ $$ = smt_newAttribute1($1); }
|
	KEYWORD attr_value
		{ $$ = smt_newAttribute2($1, $2); }
;

attribute_star:
	/* empty */
		{ $$ = smt_listCreate(); }
|
	attribute_star attribute
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

attribute_plus:
	attribute
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	attribute_plus attribute
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

attr_value:
	spec_const
		{ $$ = $1; }
|
	symbol
		{ $$ = $1; }
|
	'(' s_exp_plus ')'
		{ $$ = smt_newCompSExpression($2); }
;

s_exp:
	spec_const
		{ $$ = $1; }
|
	symbol
		{ $$ = $1; }
|
	KEYWORD
		{ $$ = $1; }
|
	'(' s_exp_plus ')'
		{ $$ = smt_newCompSExpression($2); }
;

s_exp_plus :
	s_exp 
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	s_exp_plus s_exp
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

prop_literal:
	SYMBOL 
		{ $$ = smt_newPropLiteral($1, 0); }
|
	'(' NOT SYMBOL ')'
		{ $$ = smt_newPropLiteral($3, 1); }
;

prop_literal_star:
	/* empty */
		{ $$ = smt_listCreate(); }

|
	prop_literal_star prop_literal
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

fun_decl:
	'(' symbol '(' sorted_var_star ')' sort ')'
		{ $$ = smt_newFunctionDeclaration($2, $4, $6); }
;

fun_decl_plus:
	fun_decl
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	fun_decl_plus fun_decl
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

fun_def:
	symbol '(' sorted_var_star ')' sort term
		{ $$ = smt_newFunctionDefinition(
			smt_newFunctionDeclaration($1, $3, $5), $6); }
;

symbol_star:
	/* empty */
		{ $$ = smt_listCreate(); }
|
	symbol_star symbol
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

symbol_plus:
	symbol
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	symbol_plus symbol
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

info_flag:
	KEYWORD { $$ = $1; }
;

option:
	attribute 	{ $$ = $1; }
;

theory_decl:
	'(' THEORY symbol theory_attr_plus ')'
		{ $$ = smt_newSmtTheory($3, $4); }
;

theory_attr:
	ATTR_SORTS '(' sort_symbol_decl_plus ')'
		{ $$ = smt_newAttribute2($1, 
			smt_newCompoundAttributeValue($3)); }
|
	ATTR_FUNS '(' par_fun_symbol_decl_plus ')'
		{ $$ = smt_newAttribute2($1, 
			smt_newCompoundAttributeValue($3)); }
|
	attribute 	{ $$ = $1; }
;

theory_attr_plus:
	theory_attr
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	theory_attr_plus theory_attr
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

sort_symbol_decl:
	'(' identifier NUMERAL attribute_star ')'
		{ $$ = smt_newSortSymbolDeclaration($2, $3, $4); }
;

sort_symbol_decl_plus:
	sort_symbol_decl
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	sort_symbol_decl_plus sort_symbol_decl
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

par_fun_symbol_decl:
	fun_symbol_decl
|
	'(' KW_PAR '(' symbol_plus ')' '(' identifier sort_plus attribute_star ')' ')'
		{ $$ = smt_newParamFunDeclaration($4, $7, $8, $9); }
;

par_fun_symbol_decl_plus:
	par_fun_symbol_decl
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	par_fun_symbol_decl_plus par_fun_symbol_decl
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

fun_symbol_decl:
	'(' spec_const sort attribute_star ')'
		{ $$ = smt_newSpecConstFunDeclaration($2, $3, $4); }
|
	'(' meta_spec_const sort attribute_star ')'
		{ $$ = smt_newMetaSpecConstFunDeclaration($2, $3, $4); }
|
	'(' identifier sort_plus attribute_star ')'
		{ $$ = smt_newIdentifFunDeclaration($2, $3, $4); }
;

meta_spec_const:
	META_SPEC_NUMERAL
		{ $$ = $1; }
|
	META_SPEC_DECIMAL
		{ $$ = $1; }
|
	META_SPEC_STRING
		{ $$ = $1; }
;

logic:
	'(' LOGIC symbol logic_attr_plus ')'
		{ $$ = smt_newSmtLogic($3, $4); }
;

logic_attr:
	ATTR_THEORIES '(' symbol_plus ')'
		{ $$ = smt_newAttribute2($1, smt_newCompoundAttributeValue($3)); }
|
	attribute 	{ $$ = $1; }
;

logic_attr_plus:
	logic_attr
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 
		}
|
	logic_attr_plus logic_attr
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 
		}
;

%%

int yyerror(const char *s) {
	printf("yyerror: %s\n", s);
}

int main() {
	yyparse();
}