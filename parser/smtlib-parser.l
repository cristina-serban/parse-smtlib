%{ 
#include <stdlib.h>
#include <string.h>
#include "smtlib-glue.h" 
#include "smtlib-parser.h" 

int yycolumn = 1;
#define YY_USER_ACTION yylloc.first_line = yylloc.last_line = yylineno; \
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

"_"                	{ return '_'; }
"!"                	{ return '!'; }
"as"               	{ return KW_AS; }
"let"              	{ return KW_LET; }
"exists"           	{ return KW_EXISTS; }
"forall"           	{ return KW_FORALL; }
"par"              	{ return KW_PAR; }

"("				   	{ return '('; }
")"				   	{ return ')'; }

{numeral}		   	{ 
						yylval.ptr = smt_newNumeralLiteral(
							strtol(yytext, NULL, 10), 10); 
						return NUMERAL; 
					}

{decimal}		   	{
						yylval.ptr = smt_newDecimalLiteral(
							strtod(yytext, NULL));  
						return DECIMAL; 
					}
{hexadecimal}	   	{ 
						yylval.ptr = smt_newNumeralLiteral(
							strtol(yytext+2, NULL, 16), 16); 
						return HEXADECIMAL; 
					}
{binary}		   	{
						yylval.ptr = smt_newNumeralLiteral(
							strtol(yytext+2, NULL, 2), 2); 
						return BINARY; 
					}
"not"					{ return NOT; }

"assert"		   		{ return CMD_ASSERT; }
"check-sat-assuming"	{ return CMD_CHK_SAT_ASSUM; }
"check-sat"		   		{ return CMD_CHK_SAT; }
"declare-const"		   	{ return CMD_DECL_CONST; }
"declare-fun"			{ return CMD_DECL_FUN; }
"declare-sort"	   		{ return CMD_DECL_SORT; }
"define-funs-rec"		{ return CMD_DEF_FUNS_REC; }
"define-fun-rec"		{ return CMD_DEF_FUN_REC; }
"define-fun"			{ return CMD_DEF_FUN; }
"define-sort"			{ return CMD_DEF_SORT; }
"echo"					{ return CMD_ECHO; }
"exit"					{ return CMD_EXIT; }
"get-assertions"		{ return CMD_GET_ASSERTS; }
"get-assignment"		{ return CMD_GET_ASSIGNS; }
"get-info"				{ return CMD_GET_INFO; }
"get-model"				{ return CMD_GET_MODEL; }
"get-option"			{ return CMD_GET_OPT; }
"get-proof"				{ return CMD_GET_PROOF; }
"get-unsat-assumptions"	{ return CMD_GET_UNSAT_ASSUMS; }
"get-unsat-core"		{ return CMD_GET_UNSAT_CORE; }
"get-value"				{ return CMD_GET_VALUE; }
"pop"					{ return CMD_POP; }
"push"					{ return CMD_PUSH; }
"reset-assertions"		{ return CMD_RESET_ASSERTS; }
"reset"					{ return CMD_RESET; }
"set-info"				{ return CMD_SET_INFO; }
"set-logic"				{ return CMD_SET_LOGIC; }
"set-option"			{ return CMD_SET_OPT; }

"DECIMAL"	{ 
				yylval.ptr = smt_newMetaSpecConstant(0);
				return META_SPEC_DECIMAL; 
			}
"NUMERAL"	{ 
				yylval.ptr = smt_newMetaSpecConstant(1);
				return META_SPEC_NUMERAL; 
			}
"STRING"	{ 
				yylval.ptr = smt_newMetaSpecConstant(2);
				return META_SPEC_STRING; 
			}

"theory" 	{ 
				yylval.ptr = smt_newSymbol(yytext); 
				return THEORY; 
			}
"logic" 	{ 
				yylval.ptr = smt_newSymbol(yytext); 
				return LOGIC; 
			}

":sorts"				{ 
							yylval.ptr = smt_newKeyword(yytext);
							return ATTR_SORTS; 
						}
":funs"					{ 
							yylval.ptr = smt_newKeyword(yytext);
							return ATTR_FUNS; 
						}
":theories" 			{
							yylval.ptr = smt_newKeyword(yytext); 
							return ATTR_THEORIES; 
						}

{simple_symbol}		{
						yylval.ptr = smt_newSymbol(yytext); 
						return SYMBOL; 
					}
":"{simple_symbol}	{ 
						yylval.ptr = smt_newKeyword(yytext); 
						return KEYWORD; 
					}

\"					{ BEGIN string; }
<string>\"\"   		{ yymore(); }
<string>[\n\r]+		{ yycolumn = 1; yymore(); }
<string>\"			{ 
						char *content = (char *)malloc(sizeof(char) * (yyleng - 1));
						strncpy(content, yytext, yyleng - 1);
						BEGIN 0; 
						yylval.ptr = smt_newStringLiteral(content);
						return STRING; 
					}
<string>.			{ yymore(); }

\|					{ yymore(); BEGIN quoted; }
<quoted>[\n\r]+		{ yycolumn = 1; yymore(); }
<quoted>\|			{ 
						BEGIN 0; 
						yylval.ptr = smt_newSymbol(yytext);
						return SYMBOL; 
					}
<quoted>\\			{ }
<quoted>.			{ yymore(); }

[\n\r]+				{ yycolumn = 1; }
{whitespace}		{ /*ignore*/ }
{comment}			{ /*ignore*/ }

