%{
#include <stdio.h>
#include "smtlib-glue.h"

int yylex();
int yyerror(SmtPrsr parser, const char *);

#define YYMAXDEPTH 300000
#define YYINITDEPTH 300000
%}

%locations
%error-verbose

%parse-param {SmtPrsr parser}

%union
{
	SmtPtr ptr;
	SmtList list;
};

%token KW_AS KW_LET KW_FORALL KW_EXISTS KW_PAR NOT

%token <ptr> NUMERAL DECIMAL HEXADECIMAL BINARY

%token KW_CMD_ASSERT KW_CMD_CHK_SAT KW_CMD_CHK_SAT_ASSUM KW_CMD_DECL_CONST KW_CMD_DECL_FUN KW_CMD_DECL_SORT
%token KW_CMD_DEF_FUN KW_CMD_DEF_FUN_REC KW_CMD_DEF_FUNS_REC KW_CMD_DEF_SORT KW_CMD_ECHO KW_CMD_EXIT
%token KW_CMD_GET_ASSERTS KW_CMD_GET_ASSIGNS KW_CMD_GET_INFO KW_CMD_GET_MODEL KW_CMD_GET_OPT KW_CMD_GET_PROOF
%token KW_CMD_GET_UNSAT_ASSUMS KW_CMD_GET_UNSAT_CORE KW_CMD_GET_VALUE KW_CMD_POP KW_CMD_PUSH
%token KW_CMD_RESET KW_CMD_RESET_ASSERTS KW_CMD_SET_INFO KW_CMD_SET_LOGIC KW_CMD_SET_OPT

%token <ptr> META_SPEC_DECIMAL META_SPEC_NUMERAL META_SPEC_STRING
%token <ptr> KEYWORD STRING SYMBOL THEORY LOGIC

%token <ptr> KW_ATTR_SORTS KW_ATTR_FUNS KW_ATTR_THEORIES

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
	script			{ $$ = $1; smt_setAst(parser, $1); }
|
	theory_decl		{ $$ = $1; smt_setAst(parser, $1); }
|
	logic 			{ $$ = $1; smt_setAst(parser, $1); }
;

script:
	command_plus	
		{ 
			$$ = smt_newSmtScript($1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

command_plus:
	command 				
		{ 	
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	command_plus command 	
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

command:
	'(' KW_CMD_ASSERT term ')'		
		{ 
			$$ = smt_newAssertCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_CHK_SAT ')'			
		{ 
			$$ = smt_newCheckSatCommand(); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_CHK_SAT_ASSUM '(' prop_literal_star ')' ')'		
		{ 
			$$ = smt_newCheckSatAssumCommand($4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @6.last_line;
            @$.last_column = @6.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_DECL_CONST symbol sort ')'						
		{ 
			$$ = smt_newDeclareConstCommand($3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @5.last_line;
            @$.last_column = @5.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_DECL_FUN symbol '(' sort_star ')' sort ')'
		{ 
			$$ = smt_newDeclareFunCommand($3, $5, $7); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @8.last_line;
            @$.last_column = @8.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_DECL_SORT symbol NUMERAL ')'
		{ 
			$$ = smt_newDeclareSortCommand($3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @5.last_line;
            @$.last_column = @5.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_DEF_FUNS_REC '(' fun_decl_plus ')'  '(' term_plus ')' ')'
		{ 
			$$ = smt_newDefineFunsRecCommand($4, $7); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @9.last_line;
            @$.last_column = @9.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|	
	'(' KW_CMD_DEF_FUN_REC fun_def ')'
		{ 
			$$ = smt_newDefineFunRecCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_DEF_FUN fun_def ')'
		{ 
			$$ = smt_newDefineFunCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_DEF_SORT symbol '(' symbol_star ')' sort ')'
		{ 
			$$ = smt_newDefineSortCommand($3, $5, $7); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @8.last_line;
            @$.last_column = @8.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_ECHO STRING ')'
		{ 
			$$ = smt_newEchoCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_EXIT ')'
		{ 
			$$ = smt_newExitCommand(); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_GET_ASSERTS ')'
		{ 
			$$ = smt_newGetAssertsCommand(); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_GET_ASSIGNS ')'
		{ 
			$$ = smt_newGetAssignsCommand(); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_GET_INFO info_flag ')' 
		{ 
			$$ = smt_newGetInfoCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_GET_MODEL ')'
		{ 
			$$ = smt_newGetModelCommand(); 
			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_GET_OPT KEYWORD ')'
		{ 
			$$ = smt_newGetOptionCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_GET_PROOF ')'
		{ 
			$$ = smt_newGetProofCommand(); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_GET_UNSAT_ASSUMS ')'
		{ 
			$$ = smt_newGetModelCommand(); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_GET_UNSAT_CORE ')'
		{ 
			$$ = smt_newGetUnsatCoreCommand(); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_GET_VALUE term_plus ')'
		{ 
			$$ = smt_newGetValueCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_POP NUMERAL ')'
		{ 
			$$ = smt_newPopCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_PUSH NUMERAL ')'
		{ 
			$$ = smt_newPushCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_RESET_ASSERTS ')'
		{ 
			$$ = smt_newResetAssertsCommand(); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_RESET ')'
		{ 
			$$ = smt_newResetCommand(); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_SET_INFO attribute ')'
		{ 
			$$ = smt_newSetInfoCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_SET_LOGIC symbol ')'
		{ 
			$$ = smt_newSetLogicCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
            @$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_CMD_SET_OPT option ')'
		{ 
			$$ = smt_newSetOptionCommand($3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

term:
	spec_const 			
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	qual_identifier		
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	'(' qual_identifier term_plus ')' 
		{ 
			$$ = smt_newQualifiedTerm($2, $3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_LET '(' var_binding_plus ')' term ')'
		{ 
			$$ = smt_newLetTerm($4, $6); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @7.last_line;
            @$.last_column = @7.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_FORALL '(' sorted_var_plus ')' term ')'
		{ 
			$$ = smt_newForallTerm($4, $6); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @7.last_line;
            @$.last_column = @7.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_EXISTS '(' sorted_var_plus ')' term ')'
		{ 
			$$ = smt_newExistsTerm($4, $6); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' '!' term attribute_plus ')'
		{ 
			$$ = smt_newAnnotatedTerm($3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' term ')' 
		{ 
			$$ = $2; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

term_plus:
	term 				
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	term_plus term 		
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

spec_const:
	NUMERAL 		
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	DECIMAL 		
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	HEXADECIMAL 	
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	BINARY 			
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	STRING 			
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

symbol:
	SYMBOL
		{
			$$ = $1;

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	KW_CMD_RESET
		{
			$$ = smt_newSymbol("reset");

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	NOT
		{ 
			$$ = smt_newSymbol("not"); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

qual_identifier:
	identifier 		
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' KW_AS identifier sort ')'
		{ 
			$$ = smt_newQualifiedIdentifier($3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @5.last_line;
            @$.last_column = @5.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

identifier:
	symbol 			
		{ 
			$$ = smt_newIdentifier1($1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' '_' symbol index_plus ')'
		{ 
			$$ = smt_newIdentifier2($3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @5.last_line;
            @$.last_column = @5.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

index:
	NUMERAL 	
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	symbol 		
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

index_plus:
	index 				
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	index_plus index 	
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

sort:
	identifier 	
		{ 
			$$ = smt_newSort1($1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' identifier sort_plus ')'
		{ 
			$$ = smt_newSort2($2, $3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

			smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

sort_plus:
	sort
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	sort_plus sort
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

sort_star:
	/* empty */
		{ 
			$$ = smt_listCreate();
		}
|
	sort_star sort
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			if(!@1.first_line) {
				@$.first_line = @2.first_line;
            	@$.first_column = @2.first_column;
				@$.last_line = @2.last_line;
            	@$.last_column = @2.last_column;
			} else {
				@$.first_line = @1.first_line;
            	@$.first_column = @1.first_column;
				@$.last_line = @2.last_line;
            	@$.last_column = @2.last_column;
			}
		}
;

var_binding:
	'(' symbol term ')'
		{ 
			$$ = smt_newVarBinding($2, $3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

var_binding_plus:
	var_binding
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	var_binding_plus var_binding
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

sorted_var:
	'(' symbol sort ')'
		{ 
			$$ = smt_newSortedVariable($2, $3); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

sorted_var_plus:
	sorted_var
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	sorted_var_plus sorted_var
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
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

			if(!@1.first_line) {
				@$.first_line = @2.first_line;
            	@$.first_column = @2.first_column;
				@$.last_line = @2.last_line;
            	@$.last_column = @2.last_column;
        	} else {
        		@$.first_line = @1.first_line;
            	@$.first_column = @1.first_column;
				@$.last_line = @2.last_line;
            	@$.last_column = @2.last_column;
        	}
		}
;

attribute:
	KEYWORD
		{ 
			$$ = smt_newAttribute1($1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	KEYWORD attr_value
		{ 
			$$ = smt_newAttribute2($1, $2); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

attribute_star:
	/* empty */
		{ $$ = smt_listCreate(); }
|
	attribute_star attribute
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			if(!@1.first_line) {
				@$.first_line = @2.first_line;
            	@$.first_column = @2.first_column;
				@$.last_line = @2.last_line;
            	@$.last_column = @2.last_column;
        	} else {
        		@$.first_line = @1.first_line;
            	@$.first_column = @1.first_column;
				@$.last_line = @2.last_line;
            	@$.last_column = @2.last_column;
        	}
		}
;

attribute_plus:
	attribute
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	attribute_plus attribute
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
        	@$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
        	@$.last_column = @2.last_column;
		}
;

attr_value:
	spec_const
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	symbol
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	'(' s_exp_plus ')'
		{ 
			$$ = smt_newCompSExpression($2); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

s_exp:
	spec_const
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	symbol
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	KEYWORD
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	'(' s_exp_plus ')'
		{ 
			$$ = smt_newCompSExpression($2); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @3.last_line;
            @$.last_column = @3.last_column;
		}
;

s_exp_plus :
	s_exp 
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	s_exp_plus s_exp
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

prop_literal:
	SYMBOL 
		{ 
			$$ = smt_newPropLiteral($1, 0); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' NOT SYMBOL ')'
		{ 
			$$ = smt_newPropLiteral($3, 1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

prop_literal_star:
	/* empty */
		{ $$ = smt_listCreate(); }

|
	prop_literal_star prop_literal
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			if(!@1.first_line) {
				@$.first_line = @2.first_line;
            	@$.first_column = @2.first_column;
				@$.last_line = @2.last_line;
            	@$.last_column = @2.last_column;
        	} else {
        		@$.first_line = @1.first_line;
            	@$.first_column = @1.first_column;
				@$.last_line = @2.last_line;
            	@$.last_column = @2.last_column;
        	}
		}
;

fun_decl:
	'(' symbol '(' sorted_var_star ')' sort ')'
		{ 
			$$ = smt_newFunctionDeclaration($2, $4, $6); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @7.last_line;
            @$.last_column = @7.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

fun_decl_plus:
	fun_decl
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	fun_decl_plus fun_decl
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

fun_def:
	symbol '(' sorted_var_star ')' sort term
		{ 
			$$ = smt_newFunctionDefinition(
				smt_newFunctionDeclaration($1, $3, $5), $6); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @6.last_line;
            @$.last_column = @6.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

symbol_star:
	/* empty */
		{ $$ = smt_listCreate(); }
|
	symbol_star symbol
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			if(!@1.first_line) {
				@$.first_line = @2.first_line;
            	@$.first_column = @2.first_column;
				@$.last_line = @2.last_line;
            	@$.last_column = @2.last_column;
        	} else {
        		@$.first_line = @1.first_line;
            	@$.first_column = @1.first_column;
				@$.last_line = @2.last_line;
            	@$.last_column = @2.last_column;
        	}
		}
;

symbol_plus:
	symbol
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	symbol_plus symbol
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

info_flag:
	KEYWORD 
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

option:
	attribute 	
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
;

theory_decl:
	'(' THEORY symbol theory_attr_plus ')'
		{ 
			$$ = smt_newTheory($3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @5.last_line;
            @$.last_column = @5.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

theory_attr:
	KW_ATTR_SORTS '(' sort_symbol_decl_plus ')'
		{ 
			$$ = smt_newAttribute2($1, 
				smt_newCompoundAttributeValue($3)); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	KW_ATTR_FUNS '(' par_fun_symbol_decl_plus ')'
		{ 
			$$ = smt_newAttribute2($1, 
				smt_newCompoundAttributeValue($3)); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	attribute 	
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
;

theory_attr_plus:
	theory_attr
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	theory_attr_plus theory_attr
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

sort_symbol_decl:
	'(' identifier NUMERAL attribute_star ')'
		{ 
			$$ = smt_newSortSymbolDeclaration($2, $3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @5.last_line;
            @$.last_column = @5.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

sort_symbol_decl_plus:
	sort_symbol_decl
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	sort_symbol_decl_plus sort_symbol_decl
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

par_fun_symbol_decl:
	fun_symbol_decl
|
	'(' KW_PAR '(' symbol_plus ')' '(' identifier sort_plus attribute_star ')' ')'
		{ 
			$$ = smt_newParamFunDeclaration($4, $7, $8, $9); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @11.last_line;
            @$.last_column = @11.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

par_fun_symbol_decl_plus:
	par_fun_symbol_decl
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	par_fun_symbol_decl_plus par_fun_symbol_decl
		{ 
			smt_listAdd($1, $2); 
			$$ = $1;

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column; 
		}
;

fun_symbol_decl:
	'(' spec_const sort attribute_star ')'
		{ 
			$$ = smt_newSpecConstFunDeclaration($2, $3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @5.last_line;
            @$.last_column = @5.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' meta_spec_const sort attribute_star ')'
		{ 
			$$ = smt_newMetaSpecConstFunDeclaration($2, $3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @5.last_line;
            @$.last_column = @5.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	'(' identifier sort_plus attribute_star ')'
		{ 
			$$ = smt_newIdentifFunDeclaration($2, $3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @5.last_line;
            @$.last_column = @5.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

meta_spec_const:
	META_SPEC_NUMERAL
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	META_SPEC_DECIMAL
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	META_SPEC_STRING
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

logic:
	'(' LOGIC symbol logic_attr_plus ')'
		{ 
			$$ = smt_newLogic($3, $4); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @5.last_line;
            @$.last_column = @5.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
;

logic_attr:
	KW_ATTR_THEORIES '(' symbol_plus ')'
		{ 
			$$ = smt_newAttribute2($1, smt_newCompoundAttributeValue($3)); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @4.last_line;
            @$.last_column = @4.last_column;

            smt_setLocation($$, @$.first_line, @$.last_line, @$.first_column, @$.last_column);
		}
|
	attribute 	
		{ 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
;

logic_attr_plus:
	logic_attr
		{ 
			$$ = smt_listCreate(); 
			smt_listAdd($$, $1); 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @1.last_line;
            @$.last_column = @1.last_column;
		}
|
	logic_attr_plus logic_attr
		{ 
			smt_listAdd($1, $2); 
			$$ = $1; 

			@$.first_line = @1.first_line;
            @$.first_column = @1.first_column;
			@$.last_line = @2.last_line;
            @$.last_column = @2.last_column;
		}
;

%%

int yyerror(SmtPrsr parser, const char *s) {
	smt_reportError(parser, yylloc.first_line, yylloc.first_column,
					yylloc.last_line, yylloc.last_column, s);
}