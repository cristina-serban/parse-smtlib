/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2013 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_YY_SMTLIB_PARSER_TAB_H_INCLUDED
# define YY_YY_SMTLIB_PARSER_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    KW_AS = 258,
    KW_LET = 259,
    KW_FORALL = 260,
    KW_EXISTS = 261,
    KW_PAR = 262,
    NOT = 263,
    NUMERAL = 264,
    DECIMAL = 265,
    HEXADECIMAL = 266,
    BINARY = 267,
    CMD_ASSERT = 268,
    CMD_CHK_SAT = 269,
    CMD_CHK_SAT_ASSUM = 270,
    CMD_DECL_CONST = 271,
    CMD_DECL_FUN = 272,
    CMD_DECL_SORT = 273,
    CMD_DEF_FUN = 274,
    CMD_DEF_FUN_REC = 275,
    CMD_DEF_FUNS_REC = 276,
    CMD_DEF_SORT = 277,
    CMD_ECHO = 278,
    CMD_EXIT = 279,
    CMD_GET_ASSERTS = 280,
    CMD_GET_ASSIGNS = 281,
    CMD_GET_INFO = 282,
    CMD_GET_MODEL = 283,
    CMD_GET_OPT = 284,
    CMD_GET_PROOF = 285,
    CMD_GET_UNSAT_ASSUMS = 286,
    CMD_GET_UNSAT_CORE = 287,
    CMD_GET_VALUE = 288,
    CMD_POP = 289,
    CMD_PUSH = 290,
    CMD_RESET = 291,
    CMD_RESET_ASSERTS = 292,
    CMD_SET_INFO = 293,
    CMD_SET_LOGIC = 294,
    CMD_SET_OPT = 295,
    META_SPEC_DECIMAL = 296,
    META_SPEC_NUMERAL = 297,
    META_SPEC_STRING = 298,
    KEYWORD = 299,
    STRING = 300,
    SYMBOL = 301,
    THEORY = 302,
    LOGIC = 303,
    ATTR_SORTS = 304,
    ATTR_FUNS = 305,
    ATTR_THEORIES = 306
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 18 "smtlib-parser.y" /* yacc.c:1909  */

	SmtPtr ptr;
	SmtList list;

#line 111 "smtlib-parser.tab.h" /* yacc.c:1909  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif


extern YYSTYPE yylval;
extern YYLTYPE yylloc;
int yyparse (SmtPrsr parser);

#endif /* !YY_YY_SMTLIB_PARSER_TAB_H_INCLUDED  */
