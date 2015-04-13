%{ 
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
"_"                { return '_'; }
"!"                { return '!'; }
"as"               { return KW_AS; }
"let"              { return KW_LET; }
"exists"           { return KW_EXISTS; }
"forall"           { return KW_FORALL; }
"par"              { return KW_PAR; }

"("				   { return '('; }
")"				   { return ')'; }
{numeral}		   { return NUMERAL; }
{decimal}		   { return DECIMAL; }
{hexadecimal}	   { return HEXADECIMAL; }
{binary}		   { return BINARY; }

"true"|"false"	   { return BOOL_VALUE; }

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
"get-unsat-assumptions"	{ return CMD_GET_UNSAT_ASSUM; }
"get-unsat-core"		{ return CMD_GET_UNSAT_CORE; }
"get-value"				{ return CMD_GET_VALUE; }
"pop"					{ return CMD_POP; }
"push"					{ return CMD_PUSH; }
"reset-assertions"		{ return CMD_RESET_ASSERTS; }
"reset"					{ return CMD_RESET; }
"set-info"				{ return CMD_SET_INFO; }
"set-logic"				{ return CMD_SET_LOGIC; }
"set-option"			{ return CMD_SET_OPT; }

"DECIMAL"				{ return META_SPEC_DECIMAL; }
"NUMERAL"				{ return META_SPEC_NUMERAL; }
"STRING"				{ return META_SPEC_STRING; }

":all-statistics"			{ return FLAG_ALL_STAT; }
":assertion-stack-levels"	{ return FLAG_ALL_ASSERT_STACK_LVLS; }
":authors"					{ return FLAG_AUTHORS; }
":error-behavior"			{ return FLAG_ERR_BEHAVIOR; }
":name"						{ return FLAG_NAME; }
":reason-unknown"			{ return FLAG_REASON_UNKOWN; }
":version"					{ return FLAG_VERSION; }

":diagnostic-output-channel"	{ return OPT_DIAGN_OUTPUT_CHANNEL; }	
":expand-definitions" 			{ return OPT_EXPAND_DEFS; }
":global-declarations" 			{ return OPT_GLOBAL_DECLS; }
":interactive-mode" 			{ return OPT_INTERACT_MODE; }
":print-success" 				{ return OPT_PRINT_SUCCESS; }
":produce-assertions" 			{ return OPT_PROD_ASSERTS; }
":produce-assignments" 			{ return OPT_PROD_ASSIGNS; }
":produce-models"				{ return OPT_PROD_MODELS; }
":produce-proofs"				{ return OPT_PROD_PROOFS; } 
":produce-unsat-assumptions"	{ return OPT_PROD_UNSAT_ASSUMS; } 
":produce-unsat-cores"			{ return OPT_PROD_UNSAT_CORES; } 
":random-seed"					{ return OPT_RAND_SEED; } 
":regular-output-channel"		{ return OPT_REG_OUTPUT_CHANNEL; } 
":reproducible-resource-limit"	{ return OPT_REPROD_RES_LIMIT; } 	
":verbosity" 					{ return OPT_VERBOSITY; }

"theory" 	{ return THEORY; }
"logic" 	{ return LOGIC; }

":sorts"				{ return ATTR_SORTS; }
":funs"					{ return ATTR_FUNS; }
":sorts-description" 	{ return ATTR_SORTS_DESC; }
":funs-description" 	{ return ATTR_FUNS_DESC; }
":definition"  			{ return ATTR_DEF; }
":values"  				{ return ATTR_VALUES; }
":notes"  				{ return ATTR_NOTES; }
":theories" 			{ return ATTR_THEORIES; }
":language" 			{ return ATTR_LANG; }
":extensions" 			{ return ATTR_EXTS; }

{simple_symbol}		{ return SYMBOL; }
":"{simple_symbol}	{ return KEYWORD; }

\"					{ BEGIN string; }
<string>\"\"   
<string>\"			{ BEGIN 0; return STRING; }

\|					{ BEGIN quoted; }
<quoted>\|			{ BEGIN 0; return SYMBOL; }
<quoted>\\			{ }
<quoted>.			{ }
