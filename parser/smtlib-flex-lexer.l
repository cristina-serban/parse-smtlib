%{ 
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "smtlib-glue.h" 
#include "smtlib-bison-parser.y.h"

int yycolumn = 1;
#define SET_LOCATION yylloc.first_line = yylloc.last_line = yylineno; \
yylloc.first_column = yycolumn; yylloc.last_column = yycolumn+yyleng-1; \
yycolumn += yyleng;
%}

whitespace     	[\x09\r\n \xA0]
printable_char 	[\x20-\x7E\xA0-xFF]
digit          	[0-9]
letter         	[a-zA-Z]
numeral        	0|[1-9][0-9]*
decimal        	{numeral}\.0*{numeral}
hexadecimal    	"#x"[0-9A-Fa-f]+
binary         	"#b"[01]+
special_char	[+\-/*=%?!.$_~&^<>@]

comment			";".*[\n\r]+

sym_begin      {letter}|{special_char}
sym_continue   {sym_begin}|{digit}
simple_symbol  {sym_begin}{sym_continue}*

%x string
%x quoted
%x comment

%option yylineno

%%

"_"                	{ SET_LOCATION; return '_'; }
"!"                	{ SET_LOCATION; return '!'; }
"as"               	{ SET_LOCATION; return KW_AS; }
"let"              	{ SET_LOCATION; return KW_LET; }
"exists"           	{ SET_LOCATION; return KW_EXISTS; }
"forall"           	{ SET_LOCATION; return KW_FORALL; }
"par"              	{ SET_LOCATION; return KW_PAR; }

"("				   	{ SET_LOCATION; return '('; }
")"				   	{ SET_LOCATION; return ')'; }

{numeral}		   	{ 
						SET_LOCATION;
						yylval.ptr = smt_newNumeralLiteral(
							strtol(yytext, NULL, 10), 10); 
						return NUMERAL; 
					}

{decimal}		   	{
						SET_LOCATION;
						yylval.ptr = smt_newDecimalLiteral(
							strtod(yytext, NULL));  
						return DECIMAL; 
					}
{hexadecimal}	   	{ 
						SET_LOCATION;
						yylval.ptr = smt_newNumeralLiteral(
							strtol(yytext+2, NULL, 16), 16); 
						return HEXADECIMAL; 
					}
{binary}		   	{
						SET_LOCATION;
						yylval.ptr = smt_newNumeralLiteral(
							strtol(yytext+2, NULL, 2), 2); 
						return BINARY; 
					}
"not"					{ SET_LOCATION; return NOT; }

"assert"		   		{ SET_LOCATION; return CMD_ASSERT; }
"check-sat-assuming"	{ SET_LOCATION; return CMD_CHK_SAT_ASSUM; }
"check-sat"		   		{ SET_LOCATION; return CMD_CHK_SAT; }
"declare-const"		   	{ SET_LOCATION; return CMD_DECL_CONST; }
"declare-fun"			{ SET_LOCATION; return CMD_DECL_FUN; }
"declare-sort"	   		{ SET_LOCATION; return CMD_DECL_SORT; }
"define-funs-rec"		{ SET_LOCATION; return CMD_DEF_FUNS_REC; }
"define-fun-rec"		{ SET_LOCATION; return CMD_DEF_FUN_REC; }
"define-fun"			{ SET_LOCATION; return CMD_DEF_FUN; }
"define-sort"			{ SET_LOCATION; return CMD_DEF_SORT; }
"echo"					{ SET_LOCATION; return CMD_ECHO; }
"exit"					{ SET_LOCATION; return CMD_EXIT; }
"get-assertions"		{ SET_LOCATION; return CMD_GET_ASSERTS; }
"get-assignment"		{ SET_LOCATION; return CMD_GET_ASSIGNS; }
"get-info"				{ SET_LOCATION; return CMD_GET_INFO; }
"get-model"				{ SET_LOCATION; return CMD_GET_MODEL; }
"get-option"			{ SET_LOCATION; return CMD_GET_OPT; }
"get-proof"				{ SET_LOCATION; return CMD_GET_PROOF; }
"get-unsat-assumptions"	{ SET_LOCATION; return CMD_GET_UNSAT_ASSUMS; }
"get-unsat-core"		{ SET_LOCATION; return CMD_GET_UNSAT_CORE; }
"get-value"				{ SET_LOCATION; return CMD_GET_VALUE; }
"pop"					{ SET_LOCATION; return CMD_POP; }
"push"					{ SET_LOCATION; return CMD_PUSH; }
"reset-assertions"		{ SET_LOCATION; return CMD_RESET_ASSERTS; }
"reset"					{ SET_LOCATION; return CMD_RESET; }
"set-info"				{ SET_LOCATION; return CMD_SET_INFO; }
"set-logic"				{ SET_LOCATION; return CMD_SET_LOGIC; }
"set-option"			{ SET_LOCATION; return CMD_SET_OPT; }

"DECIMAL"	{ 
				SET_LOCATION;
				yylval.ptr = smt_newMetaSpecConstant(0);
				return META_SPEC_DECIMAL; 
			}
"NUMERAL"	{ 
				SET_LOCATION;
				yylval.ptr = smt_newMetaSpecConstant(1);
				return META_SPEC_NUMERAL; 
			}
"STRING"	{ 
				SET_LOCATION;
				yylval.ptr = smt_newMetaSpecConstant(2);
				return META_SPEC_STRING; 
			}

"theory" 	{ 
				SET_LOCATION;
				yylval.ptr = smt_newSymbol(yytext); 
				return THEORY; 
			}
"logic" 	{ 
				SET_LOCATION;
				yylval.ptr = smt_newSymbol(yytext); 
				return LOGIC; 
			}

":sorts"				{ 
							SET_LOCATION;
							yylval.ptr = smt_newKeyword(yytext);
							return ATTR_SORTS; 
						}
":funs"					{ 
							SET_LOCATION;
							yylval.ptr = smt_newKeyword(yytext);
							return ATTR_FUNS; 
						}
":theories" 			{
							SET_LOCATION;
							yylval.ptr = smt_newKeyword(yytext); 
							return ATTR_THEORIES; 
						}

{simple_symbol}		{
						SET_LOCATION;
						yylval.ptr = smt_newSymbol(yytext); 
						return SYMBOL; 
					}
":"{simple_symbol}	{ 
						SET_LOCATION;
						yylval.ptr = smt_newKeyword(yytext); 
						return KEYWORD; 
					}

\"					{ BEGIN string; yymore(); }
<string>\"\"   		{ yymore(); }
<string>[\n\r]+		{ yycolumn = 1; yymore(); }
<string>\"			{ 	
						SET_LOCATION;											
						BEGIN 0; 
						yylval.ptr = smt_newStringLiteral(yytext);
						return STRING; 
					}
<string>.			{ yymore(); }

\|					{ BEGIN quoted; yymore(); }
<quoted>[\n\r]+		{ yycolumn = 1; yymore(); }
<quoted>\|			{ 
						SET_LOCATION;
						BEGIN 0; 
						yylval.ptr = smt_newSymbol(yytext);
						return SYMBOL; 
					}
<quoted>\\			{ }
<quoted>.			{ yymore(); }

[\n\r]+				{ SET_LOCATION; yycolumn = 1; }
{whitespace}		{ SET_LOCATION; /*ignore*/ }
{comment}			{ SET_LOCATION; /*ignore*/ }
