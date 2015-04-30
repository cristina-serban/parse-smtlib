/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* Copy the first part of user declarations.  */
#line 1 "smtlib-parser.y" /* yacc.c:339  */

#include <stdio.h>
#include "smtlib-glue.h"

int yylex(void);
int yyerror(const char *);

#line 74 "smtlib-parser.tab.c" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* In a future release of Bison, this section will be replaced
   by #include "smtlib-parser.tab.h".  */
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
#line 10 "smtlib-parser.y" /* yacc.c:355  */

	SmtPtr ptr;
	SmtList list;

#line 171 "smtlib-parser.tab.c" /* yacc.c:355  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_SMTLIB_PARSER_TAB_H_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 186 "smtlib-parser.tab.c" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  38
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   414

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  56
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  48
/* YYNRULES -- Number of rules.  */
#define YYNRULES  126
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  282

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   306

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    54,     2,     2,     2,     2,     2,     2,
      52,    53,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    55,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    45,    45,    47,    49,    53,    57,    63,    71,    74,
      77,    80,    83,    86,    89,    92,    95,    98,   101,   104,
     107,   110,   113,   116,   119,   122,   125,   128,   131,   134,
     137,   140,   143,   146,   149,   152,   157,   159,   161,   164,
     167,   170,   173,   178,   184,   192,   194,   196,   198,   200,
     204,   207,   212,   214,   219,   222,   227,   229,   233,   239,
     247,   250,   255,   261,   270,   272,   280,   285,   291,   299,
     304,   310,   319,   321,   329,   332,   338,   340,   348,   354,
     362,   365,   368,   373,   376,   379,   382,   387,   393,   401,
     404,   410,   413,   421,   426,   432,   440,   447,   449,   457,
     463,   471,   475,   479,   484,   488,   492,   496,   502,   510,
     515,   521,   529,   531,   536,   542,   550,   553,   556,   561,
     564,   567,   572,   577,   580,   584,   590
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "KW_AS", "KW_LET", "KW_FORALL",
  "KW_EXISTS", "KW_PAR", "NOT", "NUMERAL", "DECIMAL", "HEXADECIMAL",
  "BINARY", "CMD_ASSERT", "CMD_CHK_SAT", "CMD_CHK_SAT_ASSUM",
  "CMD_DECL_CONST", "CMD_DECL_FUN", "CMD_DECL_SORT", "CMD_DEF_FUN",
  "CMD_DEF_FUN_REC", "CMD_DEF_FUNS_REC", "CMD_DEF_SORT", "CMD_ECHO",
  "CMD_EXIT", "CMD_GET_ASSERTS", "CMD_GET_ASSIGNS", "CMD_GET_INFO",
  "CMD_GET_MODEL", "CMD_GET_OPT", "CMD_GET_PROOF", "CMD_GET_UNSAT_ASSUMS",
  "CMD_GET_UNSAT_CORE", "CMD_GET_VALUE", "CMD_POP", "CMD_PUSH",
  "CMD_RESET", "CMD_RESET_ASSERTS", "CMD_SET_INFO", "CMD_SET_LOGIC",
  "CMD_SET_OPT", "META_SPEC_DECIMAL", "META_SPEC_NUMERAL",
  "META_SPEC_STRING", "KEYWORD", "STRING", "SYMBOL", "THEORY", "LOGIC",
  "ATTR_SORTS", "ATTR_FUNS", "ATTR_THEORIES", "'('", "')'", "'!'", "'_'",
  "$accept", "smt_file", "script", "command_plus", "command", "term",
  "term_plus", "spec_const", "symbol", "qual_identifier", "identifier",
  "index", "index_plus", "sort", "sort_plus", "sort_star", "var_binding",
  "var_binding_plus", "sorted_var", "sorted_var_plus", "sorted_var_star",
  "attribute", "attribute_star", "attribute_plus", "attr_value", "s_exp",
  "s_exp_plus", "prop_literal", "prop_literal_star", "fun_decl",
  "fun_decl_plus", "fun_def", "symbol_star", "symbol_plus", "info_flag",
  "option", "theory_decl", "theory_attr", "theory_attr_plus",
  "sort_symbol_decl", "sort_symbol_decl_plus", "par_fun_symbol_decl",
  "par_fun_symbol_decl_plus", "fun_symbol_decl", "meta_spec_const",
  "logic", "logic_attr", "logic_attr_plus", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,    40,    41,    33,    95
};
# endif

#define YYPACT_NINF -210

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-210)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -30,   338,    36,  -210,     3,  -210,  -210,  -210,   278,    24,
      41,     7,     7,     7,     7,     7,    68,     7,    66,    75,
      81,    83,   103,   112,   125,   118,   132,   137,   278,   189,
     193,   151,   153,   164,     7,   164,     7,     7,  -210,   374,
    -210,  -210,  -210,  -210,  -210,  -210,  -210,  -210,    27,   169,
    -210,  -210,  -210,  -210,  -210,  -210,    67,   165,   214,   173,
     174,   175,   177,   179,   191,  -210,  -210,  -210,  -210,   192,
    -210,   199,  -210,  -210,  -210,  -210,   166,   200,   201,  -210,
    -210,   298,   213,   219,  -210,   220,   147,    -7,    89,   180,
     194,   215,     9,   278,     7,   278,  -210,   141,     5,  -210,
     226,  -210,   227,  -210,  -210,  -210,     7,  -210,   -34,  -210,
    -210,  -210,  -210,  -210,  -210,  -210,  -210,   253,  -210,  -210,
    -210,  -210,  -210,  -210,   229,   243,  -210,  -210,    -1,   244,
    -210,  -210,    95,   247,    67,   251,   252,   252,   164,   107,
     239,  -210,   303,   259,  -210,    67,  -210,    13,  -210,    53,
     261,   262,  -210,     8,  -210,   253,  -210,  -210,  -210,   225,
     263,   264,  -210,  -210,     7,  -210,  -210,   265,     7,  -210,
      78,     7,  -210,    98,   115,  -210,   -19,  -210,  -210,  -210,
      30,  -210,   271,  -210,  -210,    48,    67,  -210,    67,  -210,
    -210,   278,    67,  -210,   230,  -210,  -210,    89,  -210,   127,
     114,  -210,   129,  -210,  -210,    21,  -210,   278,   278,  -210,
      67,   278,  -210,   278,  -210,  -210,  -210,  -210,   266,  -210,
    -210,   267,   278,   168,   248,   268,  -210,   313,  -210,  -210,
     273,  -210,  -210,  -210,    67,    67,    67,  -210,  -210,  -210,
    -210,   274,   275,   276,   279,   280,  -210,  -210,  -210,    67,
     281,  -210,  -210,     7,  -210,    67,  -210,  -210,  -210,  -210,
    -210,  -210,   282,  -210,    45,    64,    59,    65,   119,  -210,
    -210,  -210,   284,  -210,  -210,  -210,    89,    67,    67,   120,
     285,  -210
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     2,     5,     6,     3,     4,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     1,     0,
       7,    51,    45,    46,    47,    48,    49,    50,     0,     0,
      36,    54,    37,    52,     9,    91,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    19,    20,    21,   101,     0,
      23,     0,    25,    26,    27,    43,     0,     0,     0,    32,
      31,    74,     0,     0,   102,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     8,     0,     0,    60,
       0,    64,     0,    72,    16,    15,     0,    94,     0,    97,
      18,    22,    24,    28,    44,    29,    30,     0,    80,    81,
      75,    33,    34,    35,     0,     0,   106,   107,     0,     0,
     124,   125,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    89,     0,     0,    92,     0,    11,     0,    13,     0,
       0,     0,    95,     0,    85,     0,    83,    84,    87,     0,
       0,     0,   103,   108,     0,   122,   126,     0,     0,    67,
       0,     0,    70,     0,     0,    78,     0,    56,    57,    58,
       0,    38,     0,    10,    62,     0,     0,    65,     0,    73,
      72,     0,     0,    98,     0,    82,    88,     0,   110,     0,
       0,   114,     0,   112,    99,     0,    53,     0,     0,    68,
       0,     0,    71,     0,    42,    79,    55,    59,     0,    61,
      63,     0,     0,     0,     0,     0,    86,     0,   104,   111,
       0,   120,   119,   121,     0,     0,     0,   105,   115,   123,
     100,     0,     0,     0,     0,     0,    90,    12,    96,     0,
       0,    17,    76,     0,    76,    76,    76,    66,    39,    69,
      40,    41,     0,    14,     0,     0,     0,     0,     0,    93,
     109,    77,     0,   116,   118,   117,     0,     0,    76,     0,
       0,   113
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -210,  -210,  -210,  -210,   322,     2,   -89,   -67,   -10,   283,
      -8,   157,  -210,   -48,  -207,  -210,   170,  -210,  -132,   202,
     152,   -24,  -209,  -210,  -210,  -136,   186,  -210,  -210,   237,
    -210,   331,  -210,    94,  -210,  -210,  -210,   221,  -210,   149,
    -210,   178,  -210,  -210,  -210,  -210,   249,  -210
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,     5,    75,    76,    50,    51,    52,
      99,   179,   180,   184,   185,   147,   169,   170,   172,   173,
     149,   271,   264,   176,   120,   158,   159,   144,    97,   107,
     108,    60,   153,   205,    69,    85,     6,   127,   128,   198,
     199,   201,   202,   203,   236,     7,   131,   132
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint16 yytable[] =
{
      53,    56,    57,    58,    59,    59,   140,    63,   100,    82,
      49,    84,    88,    41,   118,    41,    41,   189,   106,   151,
      53,    41,     1,   196,    83,    81,    86,    87,   255,    41,
      88,    89,    90,    91,   214,    41,    38,    81,    41,   177,
      53,   212,   212,    81,   129,   266,   267,   268,   124,   125,
     156,    47,   162,    47,    47,    39,    41,   133,   196,    47,
      94,   192,   126,   130,    94,    98,   186,    47,    53,   279,
     278,   119,    41,    47,   239,    41,    47,    54,   114,    92,
     134,    93,    94,   216,   139,    53,   167,    53,   156,    81,
     145,   189,   156,    55,    47,   138,   150,    41,   270,   187,
      98,   219,   224,    81,   126,   171,   188,   157,   130,    81,
      47,    64,   273,    47,   175,    41,   177,   272,   274,    98,
      62,   230,    41,    42,    43,    44,    45,   156,    65,   178,
     168,   208,    53,   234,    66,    47,    67,   220,   221,    81,
     222,   133,   114,   193,   225,   157,   129,    68,   165,   157,
     171,   211,   215,    47,   204,   231,   232,   233,   207,    46,
      47,   210,   243,    81,    81,    70,   133,   171,   213,    71,
     178,    72,   275,   280,    41,    42,    43,    44,    45,   197,
     228,   200,   237,    53,   157,    73,   254,   141,   256,   227,
      74,    81,   235,   142,   143,   240,   124,   125,    77,    53,
      53,   262,    78,    53,    79,    53,    80,   220,    81,   241,
     242,    46,    47,   244,    53,   245,    53,   101,    48,   113,
     171,   249,    96,   102,   248,   103,   114,   104,   105,   106,
     220,   109,   135,    41,    42,    43,    44,    45,    41,    42,
      43,    44,    45,   204,   110,   111,   136,    41,    42,    43,
      44,    45,   112,   115,   116,   240,    41,    42,    43,    44,
      45,    41,    42,    43,    44,    45,   121,   137,   277,   154,
      46,    47,   122,   123,   154,    46,    47,   155,   195,   146,
     148,   160,   155,   226,    46,    47,    41,    42,    43,    44,
      45,    48,   181,    46,    47,   161,   164,   154,    46,    47,
      48,   250,    94,   168,   171,   155,    41,    42,    43,    44,
      45,   182,   183,   190,   191,   197,   200,   218,   206,   246,
     247,   251,   252,    46,    47,   253,    40,   257,   258,   259,
      48,    95,   260,   261,   263,   269,   276,   217,   281,   174,
     209,   194,   223,    46,    47,   152,    61,   265,   229,   163,
     117,     8,     9,    10,    11,    12,    13,    14,    15,    16,
      17,    18,    19,    20,    21,    22,    23,    24,    25,    26,
      27,    28,    29,    30,    31,    32,    33,    34,    35,     0,
     238,   166,     0,     0,     0,    36,    37,     8,     9,    10,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    34,    35
};

static const yytype_int16 yycheck[] =
{
       8,    11,    12,    13,    14,    15,    95,    17,    56,    33,
       8,    35,     3,     8,    81,     8,     8,   149,    52,    53,
      28,     8,    52,   159,    34,    44,    36,    37,   235,     8,
       3,     4,     5,     6,    53,     8,     0,    44,     8,     9,
      48,   173,   174,    44,    51,   254,   255,   256,    49,    50,
     117,    46,    53,    46,    46,    52,     8,    52,   194,    46,
      55,    53,    86,    87,    55,    52,    53,    46,    76,   278,
     277,    81,     8,    46,    53,     8,    46,    53,    76,    52,
      88,    54,    55,    53,    94,    93,   134,    95,   155,    44,
      98,   223,   159,    52,    46,    93,   106,     8,    53,   147,
      52,    53,   191,    44,   128,    52,    53,   117,   132,    44,
      46,    45,    53,    46,   138,     8,     9,    53,    53,    52,
      52,     7,     8,     9,    10,    11,    12,   194,    53,   139,
      52,    53,   140,   200,    53,    46,    53,   185,   186,    44,
     188,    52,   140,   153,   192,   155,    51,    44,    53,   159,
      52,    53,   176,    46,   164,    41,    42,    43,   168,    45,
      46,   171,   210,    44,    44,    53,    52,    52,    53,    44,
     180,    53,    53,    53,     8,     9,    10,    11,    12,    52,
      53,    52,    53,   191,   194,    53,   234,    46,   236,   197,
      53,    44,   200,    52,    53,   205,    49,    50,     9,   207,
     208,   249,     9,   211,    53,   213,    53,   255,    44,   207,
     208,    45,    46,   211,   222,   213,   224,    52,    52,    53,
      52,    53,    53,     9,   222,    52,   224,    53,    53,    52,
     278,    52,    52,     8,     9,    10,    11,    12,     8,     9,
      10,    11,    12,   253,    53,    53,    52,     8,     9,    10,
      11,    12,    53,    53,    53,   265,     8,     9,    10,    11,
      12,     8,     9,    10,    11,    12,    53,    52,   276,    44,
      45,    46,    53,    53,    44,    45,    46,    52,    53,    53,
      53,    52,    52,    53,    45,    46,     8,     9,    10,    11,
      12,    52,    53,    45,    46,    52,    52,    44,    45,    46,
      52,    53,    55,    52,    52,    52,     8,     9,    10,    11,
      12,     8,    53,    52,    52,    52,    52,    46,    53,    53,
      53,    53,     9,    45,    46,    52,     4,    53,    53,    53,
      52,    48,    53,    53,    53,    53,    52,   180,    53,   137,
     170,   155,   190,    45,    46,   108,    15,   253,   199,   128,
      52,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    27,    28,    29,    30,    31,
      32,    33,    34,    35,    36,    37,    38,    39,    40,    -1,
     202,   132,    -1,    -1,    -1,    47,    48,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    52,    57,    58,    59,    60,    92,   101,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    47,    48,     0,    52,
      60,     8,     9,    10,    11,    12,    45,    46,    52,    61,
      63,    64,    65,    66,    53,    52,    64,    64,    64,    64,
      87,    87,    52,    64,    45,    53,    53,    53,    44,    90,
      53,    44,    53,    53,    53,    61,    62,     9,     9,    53,
      53,    44,    77,    64,    77,    91,    64,    64,     3,     4,
       5,     6,    52,    54,    55,    65,    53,    84,    52,    66,
      69,    52,     9,    52,    53,    53,    52,    85,    86,    52,
      53,    53,    53,    53,    61,    53,    53,    52,    63,    64,
      80,    53,    53,    53,    49,    50,    77,    93,    94,    51,
      77,   102,   103,    52,    66,    52,    52,    52,    61,    64,
      62,    46,    52,    53,    83,    66,    53,    71,    53,    76,
      64,    53,    85,    88,    44,    52,    63,    64,    81,    82,
      52,    52,    53,    93,    52,    53,   102,    69,    52,    72,
      73,    52,    74,    75,    75,    77,    79,     9,    64,    67,
      68,    53,     8,    53,    69,    70,    53,    69,    53,    74,
      52,    52,    53,    64,    82,    53,    81,    52,    95,    96,
      52,    97,    98,    99,    64,    89,    53,    64,    53,    72,
      64,    53,    74,    53,    53,    77,    53,    67,    46,    53,
      69,    69,    69,    76,    62,    69,    53,    66,    53,    95,
       7,    41,    42,    43,    63,    66,   100,    53,    97,    53,
      64,    61,    61,    69,    61,    61,    53,    53,    61,    53,
      53,    53,     9,    52,    69,    70,    69,    53,    53,    53,
      53,    53,    69,    53,    78,    89,    78,    78,    78,    53,
      53,    77,    53,    53,    53,    53,    52,    66,    70,    78,
      53,    53
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    56,    57,    57,    57,    58,    59,    59,    60,    60,
      60,    60,    60,    60,    60,    60,    60,    60,    60,    60,
      60,    60,    60,    60,    60,    60,    60,    60,    60,    60,
      60,    60,    60,    60,    60,    60,    61,    61,    61,    61,
      61,    61,    61,    62,    62,    63,    63,    63,    63,    63,
      64,    64,    65,    65,    66,    66,    67,    67,    68,    68,
      69,    69,    70,    70,    71,    71,    72,    73,    73,    74,
      75,    75,    76,    76,    77,    77,    78,    78,    79,    79,
      80,    80,    80,    81,    81,    81,    81,    82,    82,    83,
      83,    84,    84,    85,    86,    86,    87,    88,    88,    89,
      89,    90,    91,    92,    93,    93,    93,    94,    94,    95,
      96,    96,    97,    97,    98,    98,    99,    99,    99,   100,
     100,   100,   101,   102,   102,   103,   103
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     1,     1,     1,     1,     2,     4,     3,
       6,     5,     8,     5,     9,     4,     4,     8,     4,     3,
       3,     3,     4,     3,     4,     3,     3,     3,     4,     4,
       4,     3,     3,     4,     4,     4,     1,     1,     4,     7,
       7,     7,     5,     1,     2,     1,     1,     1,     1,     1,
       1,     1,     1,     5,     1,     5,     1,     1,     1,     2,
       1,     4,     1,     2,     0,     2,     4,     1,     2,     4,
       1,     2,     0,     2,     1,     2,     0,     2,     1,     2,
       1,     1,     3,     1,     1,     1,     3,     1,     2,     1,
       4,     0,     2,     7,     1,     2,     6,     0,     2,     1,
       2,     1,     1,     5,     4,     4,     1,     1,     2,     5,
       1,     2,     1,    11,     1,     2,     5,     5,     5,     1,
       1,     1,     5,     4,     1,     1,     2
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, int yyrule)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                                              );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yystacksize);

        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 45 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_print((yyvsp[0].ptr)); }
#line 1492 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 3:
#line 47 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_print((yyvsp[0].ptr)); }
#line 1498 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 4:
#line 49 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_print((yyvsp[0].ptr)); }
#line 1504 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 5:
#line 53 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSmtScript((yyvsp[0].list)); }
#line 1510 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 6:
#line 58 "smtlib-parser.y" /* yacc.c:1646  */
    { 	
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 1519 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 7:
#line 64 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1528 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 72 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAssertCommand((yyvsp[-1].ptr)); }
#line 1534 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 9:
#line 75 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newCheckSatCommand(); }
#line 1540 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 10:
#line 78 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newCheckSatAssumCommand((yyvsp[-2].list)); }
#line 1546 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 11:
#line 81 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDeclareConstCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); }
#line 1552 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 12:
#line 84 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDeclareFunCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 1558 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 13:
#line 87 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDeclareSortCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); }
#line 1564 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 14:
#line 90 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDefineFunsRecCommand((yyvsp[-5].list), (yyvsp[-2].list)); }
#line 1570 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 15:
#line 93 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDefineFunRecCommand((yyvsp[-1].ptr)); }
#line 1576 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 16:
#line 96 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDefineFunCommand((yyvsp[-1].ptr)); }
#line 1582 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 17:
#line 99 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDefineSortCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 1588 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 18:
#line 102 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newEchoCommand((yyvsp[-1].ptr)); }
#line 1594 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 19:
#line 105 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newExitCommand(); }
#line 1600 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 20:
#line 108 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetAssertsCommand(); }
#line 1606 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 21:
#line 111 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetAssignsCommand(); }
#line 1612 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 22:
#line 114 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetInfoCommand((yyvsp[-1].ptr)); }
#line 1618 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 23:
#line 117 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetModelCommand(); }
#line 1624 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 24:
#line 120 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetOptionCommand((yyvsp[-1].ptr)); }
#line 1630 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 25:
#line 123 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetProofCommand(); }
#line 1636 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 26:
#line 126 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetModelCommand(); }
#line 1642 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 27:
#line 129 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetUnsatCoreCommand(); }
#line 1648 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 28:
#line 132 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetValueCommand((yyvsp[-1].list)); }
#line 1654 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 29:
#line 135 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newPopCommand((yyvsp[-1].ptr)); }
#line 1660 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 30:
#line 138 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newPushCommand((yyvsp[-1].ptr)); }
#line 1666 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 31:
#line 141 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newResetAssertsCommand(); }
#line 1672 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 32:
#line 144 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newResetCommand(); }
#line 1678 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 147 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSetInfoCommand((yyvsp[-1].ptr)); }
#line 1684 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 150 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSetLogicCommand((yyvsp[-1].ptr)); }
#line 1690 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 153 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSetOptionCommand((yyvsp[-1].ptr)); }
#line 1696 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 157 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1702 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 37:
#line 159 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1708 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 38:
#line 162 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newQualifiedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 1714 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 39:
#line 165 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newLetTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 1720 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 40:
#line 168 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newForallTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 1726 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 41:
#line 171 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newExistsTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 1732 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 42:
#line 174 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAnnotatedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 1738 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 43:
#line 179 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 1747 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 44:
#line 185 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1756 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 45:
#line 192 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1762 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 46:
#line 194 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1768 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 47:
#line 196 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1774 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 48:
#line 198 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1780 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 49:
#line 200 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1786 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 50:
#line 205 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1792 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 51:
#line 208 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSymbol("not"); }
#line 1798 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 52:
#line 212 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1804 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 53:
#line 215 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newQualifiedIdentifier((yyvsp[-2].ptr), (yyvsp[-1].ptr)); }
#line 1810 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 54:
#line 220 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newIdentifier1((yyvsp[0].ptr)); }
#line 1816 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 55:
#line 223 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newIdentifier2((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 1822 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 56:
#line 227 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1828 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 57:
#line 229 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1834 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 58:
#line 234 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 1843 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 59:
#line 240 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1852 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 60:
#line 248 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSort1((yyvsp[0].ptr)); }
#line 1858 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 61:
#line 251 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSort2((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 1864 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 62:
#line 256 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 1873 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 63:
#line 262 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1882 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 64:
#line 270 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 1888 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 65:
#line 273 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1897 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 66:
#line 281 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newVarBinding((yyvsp[-2].ptr), (yyvsp[-1].ptr)); }
#line 1903 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 67:
#line 286 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 1912 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 68:
#line 292 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1921 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 69:
#line 300 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSortedVariable((yyvsp[-2].ptr), (yyvsp[-1].ptr)); }
#line 1927 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 70:
#line 305 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 1936 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 71:
#line 311 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1945 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 72:
#line 319 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 1951 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 73:
#line 322 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1960 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 74:
#line 330 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAttribute1((yyvsp[0].ptr)); }
#line 1966 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 75:
#line 333 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAttribute2((yyvsp[-1].ptr), (yyvsp[0].ptr)); }
#line 1972 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 76:
#line 338 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 1978 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 77:
#line 341 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1987 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 78:
#line 349 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 1996 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 79:
#line 355 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2005 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 80:
#line 363 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2011 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 81:
#line 366 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2017 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 82:
#line 369 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newCompSExpression((yyvsp[-1].list)); }
#line 2023 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 83:
#line 374 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2029 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 84:
#line 377 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2035 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 85:
#line 380 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2041 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 86:
#line 383 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newCompSExpression((yyvsp[-1].list)); }
#line 2047 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 87:
#line 388 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2056 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 88:
#line 394 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2065 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 89:
#line 402 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newPropLiteral((yyvsp[0].ptr), 0); }
#line 2071 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 90:
#line 405 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newPropLiteral((yyvsp[-1].ptr), 1); }
#line 2077 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 91:
#line 410 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 2083 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 92:
#line 414 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2092 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 93:
#line 422 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 2098 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 94:
#line 427 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2107 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 95:
#line 433 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2116 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 96:
#line 441 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newFunctionDefinition(
			smt_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)), (yyvsp[0].ptr)); }
#line 2123 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 97:
#line 447 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 2129 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 98:
#line 450 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2138 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 99:
#line 458 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2147 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 100:
#line 464 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2156 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 101:
#line 471 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2162 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 102:
#line 475 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2168 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 103:
#line 480 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newTheory((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2174 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 104:
#line 485 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), 
			smt_newCompoundAttributeValue((yyvsp[-1].list))); }
#line 2181 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 105:
#line 489 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), 
			smt_newCompoundAttributeValue((yyvsp[-1].list))); }
#line 2188 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 106:
#line 492 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2194 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 107:
#line 497 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2203 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 108:
#line 503 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2212 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 109:
#line 511 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSortSymbolDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2218 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 110:
#line 516 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2227 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 111:
#line 522 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2236 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 113:
#line 532 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newParamFunDeclaration((yyvsp[-7].list), (yyvsp[-4].ptr), (yyvsp[-3].list), (yyvsp[-2].list)); }
#line 2242 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 114:
#line 537 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2251 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 115:
#line 543 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2260 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 116:
#line 551 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2266 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 117:
#line 554 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newMetaSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2272 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 118:
#line 557 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newIdentifFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].list), (yyvsp[-1].list)); }
#line 2278 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 119:
#line 562 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2284 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 120:
#line 565 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2290 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 121:
#line 568 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2296 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 122:
#line 573 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newLogic((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2302 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 123:
#line 578 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), smt_newCompoundAttributeValue((yyvsp[-1].list))); }
#line 2308 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 124:
#line 580 "smtlib-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2314 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 125:
#line 585 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2323 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;

  case 126:
#line 591 "smtlib-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2332 "smtlib-parser.tab.c" /* yacc.c:1646  */
    break;


#line 2336 "smtlib-parser.tab.c" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 597 "smtlib-parser.y" /* yacc.c:1906  */


int yyerror(const char *s) {
	printf("yyerror: %s\n", s);
}

int main() {
	yyparse();
}
