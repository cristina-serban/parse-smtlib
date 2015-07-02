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

#ifndef YY_YY_SMTLIB_BISON_PARSER_TAB_H_INCLUDED
# define YY_YY_SMTLIB_BISON_PARSER_TAB_H_INCLUDED
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
    KW_MATCH = 262,
    KW_PAR = 263,
    NOT = 264,
    NUMERAL = 265,
    DECIMAL = 266,
    HEXADECIMAL = 267,
    BINARY = 268,
    KW_ASSERT = 269,
    KW_CHK_SAT = 270,
    KW_CHK_SAT_ASSUM = 271,
    KW_DECL_CONST = 272,
    KW_DECL_FUN = 273,
    KW_DECL_SORT = 274,
    KW_DEF_FUN = 275,
    KW_DEF_FUN_REC = 276,
    KW_DEF_FUNS_REC = 277,
    KW_DEF_SORT = 278,
    KW_ECHO = 279,
    KW_EXIT = 280,
    KW_GET_ASSERTS = 281,
    KW_GET_ASSIGNS = 282,
    KW_GET_INFO = 283,
    KW_GET_MODEL = 284,
    KW_GET_OPT = 285,
    KW_GET_PROOF = 286,
    KW_GET_UNSAT_ASSUMS = 287,
    KW_GET_UNSAT_CORE = 288,
    KW_GET_VALUE = 289,
    KW_POP = 290,
    KW_PUSH = 291,
    KW_RESET = 292,
    KW_RESET_ASSERTS = 293,
    KW_SET_INFO = 294,
    KW_SET_LOGIC = 295,
    KW_SET_OPT = 296,
    KW_DECL_DATATYPE = 297,
    KW_DECL_DATATYPES = 298,
    META_SPEC_DECIMAL = 299,
    META_SPEC_NUMERAL = 300,
    META_SPEC_STRING = 301,
    KEYWORD = 302,
    STRING = 303,
    SYMBOL = 304,
    THEORY = 305,
    LOGIC = 306,
    KW_ATTR_SORTS = 307,
    KW_ATTR_FUNS = 308,
    KW_ATTR_THEORIES = 309
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 18 "smtlib-bison-parser.y" /* yacc.c:1909  */

	SmtPtr ptr;
	SmtList list;

#line 114 "smtlib-bison-parser.tab.h" /* yacc.c:1909  */
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

#endif /* !YY_YY_SMTLIB_BISON_PARSER_TAB_H_INCLUDED  */
