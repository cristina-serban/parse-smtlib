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
#line 1 "smtlib-bison-parser.y" /* yacc.c:339  */

#include <stdio.h>
#include "smtlib-glue.h"

int yylex();
int yyerror(SmtPrsr parser, const char *);

#define YYMAXDEPTH 300000
#define YYINITDEPTH 300000

#line 77 "smtlib-bison-parser.tab.c" /* yacc.c:339  */

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
# define YYERROR_VERBOSE 1
#endif

/* In a future release of Bison, this section will be replaced
   by #include "smtlib-bison-parser.tab.h".  */
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
#line 18 "smtlib-bison-parser.y" /* yacc.c:355  */

	SmtPtr ptr;
	SmtList list;

#line 174 "smtlib-bison-parser.tab.c" /* yacc.c:355  */
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

/* Copy the second part of user declarations.  */

#line 203 "smtlib-bison-parser.tab.c" /* yacc.c:358  */

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
         || (defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL \
             && defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE) + sizeof (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

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
#define YYLAST   479

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  56
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  48
/* YYNRULES -- Number of rules.  */
#define YYNRULES  128
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  284

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
       0,    53,    53,    55,    57,    61,    65,    71,    79,    82,
      85,    88,    91,    94,    97,   100,   103,   106,   109,   112,
     115,   118,   121,   124,   127,   130,   133,   136,   139,   142,
     145,   148,   151,   154,   157,   160,   165,   167,   169,   172,
     175,   178,   181,   184,   189,   195,   203,   205,   207,   209,
     211,   215,   218,   221,   226,   228,   233,   236,   241,   243,
     247,   253,   261,   264,   269,   275,   284,   286,   294,   299,
     305,   313,   318,   324,   333,   335,   343,   346,   352,   354,
     362,   368,   376,   379,   382,   387,   390,   393,   396,   401,
     407,   415,   418,   424,   427,   435,   440,   446,   454,   461,
     463,   471,   477,   485,   489,   493,   498,   502,   506,   510,
     516,   524,   529,   535,   543,   545,   550,   556,   564,   567,
     570,   575,   578,   581,   586,   591,   594,   598,   604
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
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

#define YYPACT_NINF -228

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-228)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -33,   403,    21,  -228,   -29,  -228,  -228,  -228,   355,   -16,
      -9,   107,   107,   107,   107,   107,    -3,   107,    28,    25,
      39,    43,    76,    79,    94,    88,    97,   112,   355,   164,
     168,   134,   136,   154,   107,   154,   107,   107,  -228,   439,
    -228,  -228,  -228,  -228,  -228,  -228,  -228,  -228,  -228,   230,
     146,  -228,  -228,  -228,  -228,  -228,  -228,     6,   148,   195,
     156,   153,   157,   161,   162,   166,  -228,  -228,  -228,  -228,
     174,  -228,   176,  -228,  -228,  -228,  -228,    53,   177,   178,
    -228,  -228,   363,   184,   190,  -228,   191,   126,    -6,     8,
     194,   196,   198,   355,   107,   199,   355,  -228,   102,     4,
    -228,   200,  -228,   214,  -228,  -228,  -228,   107,  -228,   -35,
    -228,  -228,  -228,  -228,  -228,  -228,  -228,  -228,   350,  -228,
    -228,  -228,  -228,  -228,  -228,   216,   217,  -228,  -228,    27,
     219,  -228,  -228,    -5,   192,     6,   220,   221,   221,   154,
      66,  -228,   299,  -228,   243,   224,  -228,     6,  -228,    58,
    -228,   -17,   222,   226,  -228,    47,  -228,   350,  -228,  -228,
    -228,   252,   227,   228,  -228,  -228,   107,  -228,  -228,   233,
     107,  -228,    83,   107,  -228,   127,   129,  -228,   -19,  -228,
    -228,  -228,   113,  -228,   235,  -228,  -228,   116,     6,  -228,
       6,  -228,  -228,   355,     6,  -228,   281,  -228,  -228,     8,
    -228,   131,   213,  -228,   140,  -228,  -228,   121,  -228,   355,
     355,  -228,     6,   355,  -228,   355,  -228,  -228,  -228,  -228,
     234,  -228,  -228,   241,   355,   143,   304,   242,  -228,   274,
    -228,  -228,   247,  -228,  -228,  -228,     6,     6,     6,  -228,
    -228,  -228,  -228,   248,   249,   250,   253,   265,  -228,  -228,
    -228,     6,   266,  -228,  -228,   107,  -228,     6,  -228,  -228,
    -228,  -228,  -228,  -228,   267,  -228,    63,   125,    70,    73,
      74,  -228,  -228,  -228,   269,  -228,  -228,  -228,     8,     6,
       6,    84,   270,  -228
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
       7,    53,    46,    47,    48,    49,    52,    50,    51,     0,
       0,    36,    56,    37,    54,     9,    93,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    19,    20,    21,   103,
       0,    23,     0,    25,    26,    27,    44,     0,     0,     0,
      32,    31,    76,     0,     0,   104,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    37,     8,     0,     0,
      62,     0,    66,     0,    74,    16,    15,     0,    96,     0,
      99,    18,    22,    24,    28,    45,    29,    30,     0,    82,
      83,    77,    33,    34,    35,     0,     0,   108,   109,     0,
       0,   126,   127,     0,     0,     0,     0,     0,     0,     0,
       0,    43,     0,    91,     0,     0,    94,     0,    11,     0,
      13,     0,     0,     0,    97,     0,    87,     0,    85,    86,
      89,     0,     0,     0,   105,   110,     0,   124,   128,     0,
       0,    69,     0,     0,    72,     0,     0,    80,     0,    58,
      59,    60,     0,    38,     0,    10,    64,     0,     0,    67,
       0,    75,    74,     0,     0,   100,     0,    84,    90,     0,
     112,     0,     0,   116,     0,   114,   101,     0,    55,     0,
       0,    70,     0,     0,    73,     0,    42,    81,    57,    61,
       0,    63,    65,     0,     0,     0,     0,     0,    88,     0,
     106,   113,     0,   122,   121,   123,     0,     0,     0,   107,
     117,   125,   102,     0,     0,     0,     0,     0,    92,    12,
      98,     0,     0,    17,    78,     0,    78,    78,    78,    68,
      39,    71,    40,    41,     0,    14,     0,     0,     0,     0,
       0,    95,   111,    79,     0,   118,   120,   119,     0,     0,
      78,     0,     0,   115
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -228,  -228,  -228,  -228,   296,     2,   -90,   -71,   -10,   273,
      -8,   142,  -228,   -48,  -209,  -228,   158,  -228,  -143,   193,
     137,   -20,  -227,  -228,  -228,  -139,   171,  -228,  -228,   223,
    -228,   321,  -228,    82,  -228,  -228,  -228,   209,  -228,   138,
    -228,   139,  -228,  -228,  -228,  -228,   208,  -228
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,     5,    76,    77,    51,    52,    53,
     100,   181,   182,   186,   187,   149,   171,   172,   174,   175,
     151,   273,   266,   178,   121,   160,   161,   146,    98,   108,
     109,    61,   155,   207,    70,    86,     6,   128,   129,   200,
     201,   203,   204,   205,   238,     7,   132,   133
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint16 yytable[] =
{
      54,    57,    58,    59,    60,    60,   142,    64,   191,   101,
      50,   119,    41,    83,    41,    85,    41,   107,   153,     1,
      54,    38,   198,    39,    84,    82,    87,    88,   257,   268,
     269,   270,   214,   214,   216,   173,   190,    55,    82,    82,
      46,    54,    46,    56,    46,   130,   130,   158,   167,    63,
      48,    95,    48,   281,    48,    41,   134,   198,    99,    94,
     134,    41,    42,    43,    44,    45,    41,   127,   131,    54,
     280,    82,   120,    65,    41,   179,   125,   126,    66,   115,
     164,   135,   191,    46,   140,    54,   158,   169,    54,    46,
     158,   147,    67,    48,    46,   139,    68,   152,    47,    48,
     194,   189,    46,   226,    48,    49,   114,    82,   159,   127,
      99,   188,    48,   131,    82,    41,   272,    82,    82,   177,
      69,    41,   179,   275,    41,   158,   276,   277,    82,    41,
     180,   236,    71,    41,    54,   170,   210,   282,    72,   222,
     223,    73,   224,    46,   115,   195,   227,   159,   143,    46,
      74,   159,    46,    48,   144,   145,   206,    46,   217,    48,
     209,    46,    48,   212,   245,    75,   218,    48,    99,   221,
      82,    48,   180,    78,   241,   125,   126,    79,   274,   173,
     213,   173,   215,   199,   230,    54,   159,    80,   256,    81,
     258,   229,   202,   239,   237,   173,   251,   242,    82,    97,
     102,    54,    54,   264,   103,    54,   105,    54,   104,   222,
     106,   243,   244,   107,   110,   246,    54,   247,    54,   111,
     232,    41,    42,    43,    44,    45,   250,   112,   115,   113,
     116,   117,   222,    89,    90,    91,    92,   122,    41,    42,
      43,    44,    45,   123,   124,   206,   136,    94,   137,    46,
     138,   184,   141,   148,   233,   234,   235,   242,    47,    48,
      41,    42,    43,    44,    45,   134,    46,   150,   162,   163,
     279,   166,   170,   173,   192,    47,    48,   185,   193,   199,
     202,   220,    49,   254,    93,    94,   208,   248,    46,    41,
      42,    43,    44,    45,   249,   253,   156,    47,    48,   255,
      40,   259,   260,   261,   157,   197,   262,    41,    42,    43,
      44,    45,    41,    42,    43,    44,    45,    46,   263,   265,
     271,   278,    96,   283,   219,   156,    47,    48,   196,   225,
     211,   176,   154,   157,   228,    46,    62,   267,   165,   231,
      46,   168,     0,   240,    47,    48,     0,     0,     0,    47,
      48,    49,   183,     0,     0,     0,    49,   252,    41,    42,
      43,    44,    45,    41,    42,    43,    44,    45,     0,     0,
       0,    41,    42,    43,    44,    45,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    46,     0,     0,     0,
       0,    46,     0,     0,   156,    47,    48,     0,     0,    46,
      47,    48,   157,     0,     0,     0,     0,    49,    47,    48,
       0,     0,     0,     0,     0,   118,     8,     9,    10,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    27,    28,    29,    30,    31,
      32,    33,    34,    35,     0,     0,     0,     0,     0,     0,
      36,    37,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    34,    35
};

static const yytype_int16 yycheck[] =
{
       8,    11,    12,    13,    14,    15,    96,    17,   151,    57,
       8,    82,     8,    33,     8,    35,     8,    52,    53,    52,
      28,     0,   161,    52,    34,    44,    36,    37,   237,   256,
     257,   258,   175,   176,    53,    52,    53,    53,    44,    44,
      36,    49,    36,    52,    36,    51,    51,   118,    53,    52,
      46,    49,    46,   280,    46,     8,    52,   196,    52,    55,
      52,     8,     9,    10,    11,    12,     8,    87,    88,    77,
     279,    44,    82,    45,     8,     9,    49,    50,    53,    77,
      53,    89,   225,    36,    94,    93,   157,   135,    96,    36,
     161,    99,    53,    46,    36,    93,    53,   107,    45,    46,
      53,   149,    36,   193,    46,    52,    53,    44,   118,   129,
      52,    53,    46,   133,    44,     8,    53,    44,    44,   139,
      44,     8,     9,    53,     8,   196,    53,    53,    44,     8,
     140,   202,    53,     8,   142,    52,    53,    53,    44,   187,
     188,    53,   190,    36,   142,   155,   194,   157,    46,    36,
      53,   161,    36,    46,    52,    53,   166,    36,   178,    46,
     170,    36,    46,   173,   212,    53,    53,    46,    52,    53,
      44,    46,   182,     9,    53,    49,    50,     9,    53,    52,
      53,    52,    53,    52,    53,   193,   196,    53,   236,    53,
     238,   199,    52,    53,   202,    52,    53,   207,    44,    53,
      52,   209,   210,   251,     9,   213,    53,   215,    52,   257,
      53,   209,   210,    52,    52,   213,   224,   215,   226,    53,
       7,     8,     9,    10,    11,    12,   224,    53,   226,    53,
      53,    53,   280,     3,     4,     5,     6,    53,     8,     9,
      10,    11,    12,    53,    53,   255,    52,    55,    52,    36,
      52,     8,    53,    53,    41,    42,    43,   267,    45,    46,
       8,     9,    10,    11,    12,    52,    36,    53,    52,    52,
     278,    52,    52,    52,    52,    45,    46,    53,    52,    52,
      52,    46,    52,     9,    54,    55,    53,    53,    36,     8,
       9,    10,    11,    12,    53,    53,    44,    45,    46,    52,
       4,    53,    53,    53,    52,    53,    53,     8,     9,    10,
      11,    12,     8,     9,    10,    11,    12,    36,    53,    53,
      53,    52,    49,    53,   182,    44,    45,    46,   157,   192,
     172,   138,   109,    52,    53,    36,    15,   255,   129,   201,
      36,   133,    -1,   204,    45,    46,    -1,    -1,    -1,    45,
      46,    52,    53,    -1,    -1,    -1,    52,    53,     8,     9,
      10,    11,    12,     8,     9,    10,    11,    12,    -1,    -1,
      -1,     8,     9,    10,    11,    12,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    36,    -1,    -1,    -1,
      -1,    36,    -1,    -1,    44,    45,    46,    -1,    -1,    36,
      45,    46,    52,    -1,    -1,    -1,    -1,    52,    45,    46,
      -1,    -1,    -1,    -1,    -1,    52,    13,    14,    15,    16,
      17,    18,    19,    20,    21,    22,    23,    24,    25,    26,
      27,    28,    29,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    -1,    -1,    -1,    -1,    -1,    -1,
      47,    48,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    52,    57,    58,    59,    60,    92,   101,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    47,    48,     0,    52,
      60,     8,     9,    10,    11,    12,    36,    45,    46,    52,
      61,    63,    64,    65,    66,    53,    52,    64,    64,    64,
      64,    87,    87,    52,    64,    45,    53,    53,    53,    44,
      90,    53,    44,    53,    53,    53,    61,    62,     9,     9,
      53,    53,    44,    77,    64,    77,    91,    64,    64,     3,
       4,     5,     6,    54,    55,    61,    65,    53,    84,    52,
      66,    69,    52,     9,    52,    53,    53,    52,    85,    86,
      52,    53,    53,    53,    53,    61,    53,    53,    52,    63,
      64,    80,    53,    53,    53,    49,    50,    77,    93,    94,
      51,    77,   102,   103,    52,    66,    52,    52,    52,    61,
      64,    53,    62,    46,    52,    53,    83,    66,    53,    71,
      53,    76,    64,    53,    85,    88,    44,    52,    63,    64,
      81,    82,    52,    52,    53,    93,    52,    53,   102,    69,
      52,    72,    73,    52,    74,    75,    75,    77,    79,     9,
      64,    67,    68,    53,     8,    53,    69,    70,    53,    69,
      53,    74,    52,    52,    53,    64,    82,    53,    81,    52,
      95,    96,    52,    97,    98,    99,    64,    89,    53,    64,
      53,    72,    64,    53,    74,    53,    53,    77,    53,    67,
      46,    53,    69,    69,    69,    76,    62,    69,    53,    66,
      53,    95,     7,    41,    42,    43,    63,    66,   100,    53,
      97,    53,    64,    61,    61,    69,    61,    61,    53,    53,
      61,    53,    53,    53,     9,    52,    69,    70,    69,    53,
      53,    53,    53,    53,    69,    53,    78,    89,    78,    78,
      78,    53,    53,    77,    53,    53,    53,    53,    52,    66,
      70,    78,    53,    53
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    56,    57,    57,    57,    58,    59,    59,    60,    60,
      60,    60,    60,    60,    60,    60,    60,    60,    60,    60,
      60,    60,    60,    60,    60,    60,    60,    60,    60,    60,
      60,    60,    60,    60,    60,    60,    61,    61,    61,    61,
      61,    61,    61,    61,    62,    62,    63,    63,    63,    63,
      63,    64,    64,    64,    65,    65,    66,    66,    67,    67,
      68,    68,    69,    69,    70,    70,    71,    71,    72,    73,
      73,    74,    75,    75,    76,    76,    77,    77,    78,    78,
      79,    79,    80,    80,    80,    81,    81,    81,    81,    82,
      82,    83,    83,    84,    84,    85,    86,    86,    87,    88,
      88,    89,    89,    90,    91,    92,    93,    93,    93,    94,
      94,    95,    96,    96,    97,    97,    98,    98,    99,    99,
      99,   100,   100,   100,   101,   102,   102,   103,   103
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     1,     1,     1,     1,     2,     4,     3,
       6,     5,     8,     5,     9,     4,     4,     8,     4,     3,
       3,     3,     4,     3,     4,     3,     3,     3,     4,     4,
       4,     3,     3,     4,     4,     4,     1,     1,     4,     7,
       7,     7,     5,     3,     1,     2,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     5,     1,     5,     1,     1,
       1,     2,     1,     4,     1,     2,     0,     2,     4,     1,
       2,     4,     1,     2,     0,     2,     1,     2,     0,     2,
       1,     2,     1,     1,     3,     1,     1,     1,     3,     1,
       2,     1,     4,     0,     2,     7,     1,     2,     6,     0,
       2,     1,     2,     1,     1,     5,     4,     4,     1,     1,
       2,     5,     1,     2,     1,    11,     1,     2,     5,     5,
       5,     1,     1,     1,     5,     4,     1,     1,     2
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
      yyerror (parser, YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                                \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;        \
          (Current).first_column = YYRHSLOC (Rhs, 1).first_column;      \
          (Current).last_line    = YYRHSLOC (Rhs, N).last_line;         \
          (Current).last_column  = YYRHSLOC (Rhs, N).last_column;       \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).first_line   = (Current).last_line   =              \
            YYRHSLOC (Rhs, 0).last_line;                                \
          (Current).first_column = (Current).last_column =              \
            YYRHSLOC (Rhs, 0).last_column;                              \
        }                                                               \
    while (0)
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K])


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


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static unsigned
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp)
{
  unsigned res = 0;
  int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
  if (0 <= yylocp->first_line)
    {
      res += YYFPRINTF (yyo, "%d", yylocp->first_line);
      if (0 <= yylocp->first_column)
        res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
    }
  if (0 <= yylocp->last_line)
    {
      if (yylocp->first_line < yylocp->last_line)
        {
          res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
          if (0 <= end_col)
            res += YYFPRINTF (yyo, ".%d", end_col);
        }
      else if (0 <= end_col && yylocp->first_column < end_col)
        res += YYFPRINTF (yyo, "-%d", end_col);
    }
  return res;
 }

#  define YY_LOCATION_PRINT(File, Loc)          \
  yy_location_print_ (File, &(Loc))

# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value, Location, parser); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, SmtPrsr parser)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  YYUSE (yylocationp);
  YYUSE (parser);
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
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, SmtPrsr parser)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  YY_LOCATION_PRINT (yyoutput, *yylocationp);
  YYFPRINTF (yyoutput, ": ");
  yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, parser);
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
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, SmtPrsr parser)
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
                       , &(yylsp[(yyi + 1) - (yynrhs)])                       , parser);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule, parser); \
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
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, SmtPrsr parser)
{
  YYUSE (yyvaluep);
  YYUSE (yylocationp);
  YYUSE (parser);
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
/* Location data for the lookahead symbol.  */
YYLTYPE yylloc
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
  = { 1, 1, 1, 1 }
# endif
;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (SmtPrsr parser)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.
       'yyls': related to locations.

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

    /* The location stack.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls;
    YYLTYPE *yylsp;

    /* The locations where the error started and ended.  */
    YYLTYPE yyerror_range[3];

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yylsp = yyls = yylsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  yylsp[0] = yylloc;
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
        YYLTYPE *yyls1 = yyls;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yyls1, yysize * sizeof (*yylsp),
                    &yystacksize);

        yyls = yyls1;
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
        YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

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
  *++yylsp = yylloc;
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

  /* Default location.  */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 53 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_setAst(parser, (yyvsp[0].ptr)); }
#line 1618 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 3:
#line 55 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_setAst(parser, (yyvsp[0].ptr)); }
#line 1624 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 4:
#line 57 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_setAst(parser, (yyvsp[0].ptr)); }
#line 1630 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 5:
#line 61 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSmtScript((yyvsp[0].list)); }
#line 1636 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 6:
#line 66 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 	
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 1645 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 7:
#line 72 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1654 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 80 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAssertCommand((yyvsp[-1].ptr)); }
#line 1660 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 9:
#line 83 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newCheckSatCommand(); }
#line 1666 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 10:
#line 86 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newCheckSatAssumCommand((yyvsp[-2].list)); }
#line 1672 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 11:
#line 89 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDeclareConstCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); }
#line 1678 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 12:
#line 92 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDeclareFunCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 1684 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 13:
#line 95 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDeclareSortCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); }
#line 1690 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 14:
#line 98 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDefineFunsRecCommand((yyvsp[-5].list), (yyvsp[-2].list)); }
#line 1696 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 15:
#line 101 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDefineFunRecCommand((yyvsp[-1].ptr)); }
#line 1702 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 16:
#line 104 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDefineFunCommand((yyvsp[-1].ptr)); }
#line 1708 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 17:
#line 107 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newDefineSortCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 1714 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 18:
#line 110 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newEchoCommand((yyvsp[-1].ptr)); }
#line 1720 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 19:
#line 113 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newExitCommand(); }
#line 1726 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 20:
#line 116 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetAssertsCommand(); }
#line 1732 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 21:
#line 119 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetAssignsCommand(); }
#line 1738 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 22:
#line 122 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetInfoCommand((yyvsp[-1].ptr)); }
#line 1744 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 23:
#line 125 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetModelCommand(); }
#line 1750 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 24:
#line 128 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetOptionCommand((yyvsp[-1].ptr)); }
#line 1756 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 25:
#line 131 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetProofCommand(); }
#line 1762 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 26:
#line 134 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetModelCommand(); }
#line 1768 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 27:
#line 137 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetUnsatCoreCommand(); }
#line 1774 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 28:
#line 140 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newGetValueCommand((yyvsp[-1].list)); }
#line 1780 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 29:
#line 143 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newPopCommand((yyvsp[-1].ptr)); }
#line 1786 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 30:
#line 146 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newPushCommand((yyvsp[-1].ptr)); }
#line 1792 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 31:
#line 149 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newResetAssertsCommand(); }
#line 1798 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 32:
#line 152 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newResetCommand(); }
#line 1804 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 155 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSetInfoCommand((yyvsp[-1].ptr)); }
#line 1810 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 158 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSetLogicCommand((yyvsp[-1].ptr)); }
#line 1816 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 161 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSetOptionCommand((yyvsp[-1].ptr)); }
#line 1822 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 165 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1828 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 37:
#line 167 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1834 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 38:
#line 170 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newQualifiedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 1840 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 39:
#line 173 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newLetTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 1846 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 40:
#line 176 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newForallTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 1852 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 41:
#line 179 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newExistsTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 1858 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 42:
#line 182 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAnnotatedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 1864 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 43:
#line 185 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[-1].ptr); }
#line 1870 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 44:
#line 190 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 1879 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 45:
#line 196 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1888 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 46:
#line 203 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1894 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 47:
#line 205 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1900 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 48:
#line 207 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1906 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 49:
#line 209 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1912 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 50:
#line 211 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1918 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 51:
#line 216 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1924 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 52:
#line 219 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSymbol("reset"); }
#line 1930 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 53:
#line 222 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSymbol("not"); }
#line 1936 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 54:
#line 226 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1942 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 55:
#line 229 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newQualifiedIdentifier((yyvsp[-2].ptr), (yyvsp[-1].ptr)); }
#line 1948 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 56:
#line 234 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newIdentifier1((yyvsp[0].ptr)); }
#line 1954 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 57:
#line 237 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newIdentifier2((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 1960 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 58:
#line 241 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1966 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 59:
#line 243 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 1972 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 60:
#line 248 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 1981 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 61:
#line 254 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 1990 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 62:
#line 262 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSort1((yyvsp[0].ptr)); }
#line 1996 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 63:
#line 265 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSort2((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2002 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 64:
#line 270 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2011 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 65:
#line 276 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2020 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 66:
#line 284 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 2026 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 67:
#line 287 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2035 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 68:
#line 295 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newVarBinding((yyvsp[-2].ptr), (yyvsp[-1].ptr)); }
#line 2041 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 69:
#line 300 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2050 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 70:
#line 306 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2059 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 71:
#line 314 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSortedVariable((yyvsp[-2].ptr), (yyvsp[-1].ptr)); }
#line 2065 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 72:
#line 319 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2074 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 73:
#line 325 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2083 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 74:
#line 333 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 2089 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 75:
#line 336 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2098 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 76:
#line 344 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAttribute1((yyvsp[0].ptr)); }
#line 2104 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 77:
#line 347 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAttribute2((yyvsp[-1].ptr), (yyvsp[0].ptr)); }
#line 2110 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 78:
#line 352 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 2116 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 79:
#line 355 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2125 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 80:
#line 363 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2134 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 81:
#line 369 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2143 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 82:
#line 377 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2149 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 83:
#line 380 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2155 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 84:
#line 383 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newCompSExpression((yyvsp[-1].list)); }
#line 2161 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 85:
#line 388 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2167 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 86:
#line 391 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2173 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 87:
#line 394 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2179 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 88:
#line 397 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newCompSExpression((yyvsp[-1].list)); }
#line 2185 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 89:
#line 402 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2194 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 90:
#line 408 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2203 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 91:
#line 416 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newPropLiteral((yyvsp[0].ptr), 0); }
#line 2209 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 92:
#line 419 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newPropLiteral((yyvsp[-1].ptr), 1); }
#line 2215 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 93:
#line 424 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 2221 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 94:
#line 428 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2230 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 95:
#line 436 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); }
#line 2236 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 96:
#line 441 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2245 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 97:
#line 447 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2254 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 98:
#line 455 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newFunctionDefinition(
			smt_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)), (yyvsp[0].ptr)); }
#line 2261 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 99:
#line 461 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 2267 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 100:
#line 464 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2276 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 101:
#line 472 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2285 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 102:
#line 478 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2294 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 103:
#line 485 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2300 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 104:
#line 489 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2306 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 105:
#line 494 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newTheory((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2312 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 106:
#line 499 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), 
			smt_newCompoundAttributeValue((yyvsp[-1].list))); }
#line 2319 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 107:
#line 503 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), 
			smt_newCompoundAttributeValue((yyvsp[-1].list))); }
#line 2326 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 108:
#line 506 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2332 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 109:
#line 511 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2341 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 110:
#line 517 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2350 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 111:
#line 525 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSortSymbolDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2356 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 112:
#line 530 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2365 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 113:
#line 536 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2374 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 115:
#line 546 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newParamFunDeclaration((yyvsp[-7].list), (yyvsp[-4].ptr), (yyvsp[-3].list), (yyvsp[-2].list)); }
#line 2380 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 116:
#line 551 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2389 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 117:
#line 557 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2398 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 118:
#line 565 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2404 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 119:
#line 568 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newMetaSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2410 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 120:
#line 571 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newIdentifFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].list), (yyvsp[-1].list)); }
#line 2416 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 121:
#line 576 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2422 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 122:
#line 579 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2428 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 123:
#line 582 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2434 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 124:
#line 587 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newLogic((yyvsp[-2].ptr), (yyvsp[-1].list)); }
#line 2440 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 125:
#line 592 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), smt_newCompoundAttributeValue((yyvsp[-1].list))); }
#line 2446 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 126:
#line 594 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); }
#line 2452 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 127:
#line 599 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 
		}
#line 2461 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 128:
#line 605 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 
		}
#line 2470 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;


#line 2474 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
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
  *++yylsp = yyloc;

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
      yyerror (parser, YY_("syntax error"));
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
        yyerror (parser, yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }

  yyerror_range[1] = yylloc;

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
                      yytoken, &yylval, &yylloc, parser);
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

  yyerror_range[1] = yylsp[1-yylen];
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

      yyerror_range[1] = *yylsp;
      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp, yylsp, parser);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  yyerror_range[2] = yylloc;
  /* Using YYLLOC is tempting, but would change the location of
     the lookahead.  YYLOC is available though.  */
  YYLLOC_DEFAULT (yyloc, yyerror_range, 2);
  *++yylsp = yyloc;

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
  yyerror (parser, YY_("memory exhausted"));
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
                  yytoken, &yylval, &yylloc, parser);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp, yylsp, parser);
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
#line 611 "smtlib-bison-parser.y" /* yacc.c:1906  */


int yyerror(SmtPrsr parser, const char *s) {
	smt_reportError(parser, yylloc.first_line, yylloc.first_column,
					yylloc.last_line, yylloc.last_column, s);
}
