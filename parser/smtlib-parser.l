%{ 
#include <stdlib.h>
#include "smtlib-glue.h" 
#include "smtlib-parser.h" 
%}

whitespace     [\x09\r\n \xA0]
printable_char [\x20-\x7E\xA0-xFF]
digit          [0-9]
letter         [a-zA-Z]
numeral        0|[1-9][0-9]*
decimal        {numeral}.0*{numeral}
hexadecimal    "#x"[0-9A-Fa-f]+
binary         "#b"[01]+
special_char  [~!@$%^&*_\-+=.?/]

sym_begin      {letter}|{special_char}
sym_continue   {sym_begin}|{digit}
simple_symbol  {sym_begin}{sym_continue}*

%x string
%x quoted

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
						yylval.ptr = smt_newNumeralLiteral(strtol(yytext, NULL, 10)); 
						return NUMERAL; 
					}
{decimal}		   	{
						yylval.ptr = smt_newDecimalLiteral(strtod(yytext, NULL));  
						return DECIMAL; 
					}
{hexadecimal}	   	{ 
						yylval.ptr = smt_newNumeralLiteral(strtol(yytext+2, NULL, 16)); 
						return HEXADECIMAL; 
					}
{binary}		   	{
						yylval.ptr = smt_newNumeralLiteral(strtol(yytext+2, NULL, 2)); 
						return BINARY; 
					}

"true"	{ 
			yylval.ptr = smt_newBooleanValue(1); 
			return BOOL_VALUE; 
		}

"false"	{
			yylval.ptr = smt_newBooleanValue(0); 
			return BOOL_VALUE;
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

":diagnostic-output-channel" 	{
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_DIAGN_OUTPUT_CHANNEL; 
								}	
":expand-definitions" 			{
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_EXPAND_DEFS; 
								}
":global-declarations"  		{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_GLOBAL_DECLS; 
								}
":interactive-mode"  			{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_INTERACT_MODE; 
								}
":print-success" 				{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_PRINT_SUCCESS; 
								}
":produce-assertions" 			{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_PROD_ASSERTS; 
								}
":produce-assignments" 			{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_PROD_ASSIGNS; 
								}
":produce-models" 				{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_PROD_MODELS; 
								}
":produce-proofs" 				{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_PROD_PROOFS; 
								} 
":produce-unsat-assumptions" 	{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_PROD_UNSAT_ASSUMS; 
								} 
":produce-unsat-cores"			{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_PROD_UNSAT_CORES; 
								} 
":random-seed" 					{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_RAND_SEED; 
								} 
":regular-output-channel"		{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_REG_OUTPUT_CHANNEL; 
								} 
":reproducible-resource-limit" 	{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_REPROD_RES_LIMIT; 
								} 	
":verbosity" 					{ 
									yylval.ptr = smt_newKeyword(yytext); 
									return OPT_VERBOSITY; 
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
":sorts-description" 	{ 
							yylval.ptr = smt_newKeyword(yytext);
							return ATTR_SORTS_DESC; 
						}
":funs-description" 	{ 
							yylval.ptr = smt_newKeyword(yytext);
							return ATTR_FUNS_DESC; 
						}
":definition"  			{ 
							yylval.ptr = smt_newKeyword(yytext);
							return ATTR_DEF; 
						}
":values"  				{ 
							yylval.ptr = smt_newKeyword(yytext);
							return ATTR_VALUES; 
						}
":notes"  				{
							yylval.ptr = smt_newKeyword(yytext); 
							return ATTR_NOTES; 
						}
":theories" 			{
							yylval.ptr = smt_newKeyword(yytext); 
							return ATTR_THEORIES; 
						}
":language" 			{ 
							yylval.ptr = smt_newKeyword(yytext);
							return ATTR_LANG; 
						}
":extensions" 			{
							yylval.ptr = smt_newKeyword(yytext); 
							return ATTR_EXTS; 
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
<string>\"\"   
<string>\"			{ 
						BEGIN 0; 
						yylval.ptr = smt_newStringLiteral(yytext);
						return STRING; 
					}

\|					{ BEGIN quoted; }
<quoted>\|			{ 
						BEGIN 0; 
						yylval.ptr = smt_newSymbol(yytext);
						return SYMBOL; 
					}
<quoted>\\			{ }
<quoted>.			{ }
