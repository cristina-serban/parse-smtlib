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
#line 18 "smtlib-bison-parser.y" /* yacc.c:355  */

	SmtPtr ptr;
	SmtList list;

#line 177 "smtlib-bison-parser.tab.c" /* yacc.c:355  */
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

#line 206 "smtlib-bison-parser.tab.c" /* yacc.c:358  */

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
#define YYFINAL  40
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   605

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  59
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  60
/* YYNRULES -- Number of rules.  */
#define YYNRULES  152
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  350

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   309

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    57,     2,     2,     2,     2,     2,     2,
      55,    56,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    58,     2,     2,     2,     2,
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
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    56,    56,    58,    60,    64,    78,    89,   102,   114,
     126,   138,   150,   162,   174,   186,   198,   210,   222,   234,
     246,   258,   270,   282,   294,   306,   317,   329,   341,   353,
     365,   377,   389,   401,   413,   425,   437,   449,   463,   474,
     487,   499,   513,   524,   537,   552,   556,   576,   590,   601,
     614,   628,   638,   648,   660,   672,   684,   696,   708,   720,
     734,   745,   758,   769,   782,   796,   806,   820,   830,   844,
     856,   868,   880,   892,   906,   918,   930,   942,   956,   966,
     980,   990,  1004,  1016,  1028,  1039,  1052,  1062,  1076,  1087,
    1101,  1105,  1125,  1139,  1150,  1163,  1177,  1188,  1202,  1204,
    1224,  1236,  1251,  1253,  1273,  1284,  1297,  1307,  1317,  1331,
    1341,  1351,  1361,  1375,  1386,  1399,  1411,  1426,  1429,  1449,
    1463,  1474,  1487,  1503,  1505,  1525,  1536,  1549,  1563,  1575,
    1589,  1602,  1615,  1627,  1638,  1651,  1665,  1676,  1689,  1691,
    1705,  1716,  1729,  1741,  1753,  1767,  1779,  1791,  1805,  1819,
    1831,  1843,  1854
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "KW_AS", "KW_LET", "KW_FORALL",
  "KW_EXISTS", "KW_MATCH", "KW_PAR", "NOT", "NUMERAL", "DECIMAL",
  "HEXADECIMAL", "BINARY", "KW_ASSERT", "KW_CHK_SAT", "KW_CHK_SAT_ASSUM",
  "KW_DECL_CONST", "KW_DECL_FUN", "KW_DECL_SORT", "KW_DEF_FUN",
  "KW_DEF_FUN_REC", "KW_DEF_FUNS_REC", "KW_DEF_SORT", "KW_ECHO", "KW_EXIT",
  "KW_GET_ASSERTS", "KW_GET_ASSIGNS", "KW_GET_INFO", "KW_GET_MODEL",
  "KW_GET_OPT", "KW_GET_PROOF", "KW_GET_UNSAT_ASSUMS", "KW_GET_UNSAT_CORE",
  "KW_GET_VALUE", "KW_POP", "KW_PUSH", "KW_RESET", "KW_RESET_ASSERTS",
  "KW_SET_INFO", "KW_SET_LOGIC", "KW_SET_OPT", "KW_DECL_DATATYPE",
  "KW_DECL_DATATYPES", "META_SPEC_DECIMAL", "META_SPEC_NUMERAL",
  "META_SPEC_STRING", "KEYWORD", "STRING", "SYMBOL", "THEORY", "LOGIC",
  "KW_ATTR_SORTS", "KW_ATTR_FUNS", "KW_ATTR_THEORIES", "'('", "')'", "'!'",
  "'_'", "$accept", "smt_file", "script", "command_plus", "command",
  "datatype_decl_plus", "datatype_decl", "constructor_decl_plus",
  "constructor_decl", "selector_decl_star", "selector_decl",
  "sort_decl_plus", "sort_decl", "term", "term_plus", "match_case_plus",
  "match_case", "pattern", "qual_constructor", "spec_const", "symbol",
  "qual_identifier", "identifier", "index", "index_plus", "sort",
  "sort_plus", "sort_star", "var_binding", "var_binding_plus",
  "sorted_var", "sorted_var_plus", "sorted_var_star", "attribute",
  "attribute_star", "attribute_plus", "attr_value", "s_exp", "s_exp_plus",
  "prop_literal", "prop_literal_star", "fun_decl", "fun_decl_plus",
  "fun_def", "symbol_star", "symbol_plus", "info_flag", "option",
  "theory_decl", "theory_attr", "theory_attr_plus", "sort_symbol_decl",
  "sort_symbol_decl_plus", "par_fun_symbol_decl",
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
     305,   306,   307,   308,   309,    40,    41,    33,    95
};
# endif

#define YYPACT_NINF -290

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-290)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -33,   524,    26,  -290,    -6,  -290,  -290,  -290,   447,   -15,
       6,   103,   103,   103,   103,   103,     8,   103,    -4,    30,
      38,    53,    80,    86,   100,    98,   101,   107,   447,   138,
     158,   122,   127,   140,   103,   140,   136,   143,   103,   103,
    -290,   562,  -290,  -290,  -290,  -290,  -290,  -290,  -290,  -290,
    -290,    27,  -290,   137,  -290,  -290,  -290,  -290,  -290,  -290,
     104,   149,   185,   154,   155,   157,   160,   175,   182,  -290,
    -290,  -290,  -290,   184,  -290,   188,  -290,  -290,  -290,  -290,
     368,   190,   198,  -290,  -290,   460,   203,   212,  -290,   213,
     208,   218,   447,   120,    92,   215,   216,   220,   221,   447,
     447,   103,   223,   447,  -290,    95,   364,  -290,   225,  -290,
     226,  -290,  -290,  -290,   103,  -290,   -31,  -290,  -290,  -290,
    -290,  -290,  -290,  -290,  -290,   381,  -290,  -290,  -290,  -290,
    -290,  -290,   232,    52,  -290,  -290,    74,  -290,   233,   234,
    -290,  -290,    40,   235,  -290,  -290,    -2,   238,   104,   242,
     243,   243,   244,   140,    68,  -290,   397,  -290,   284,   248,
    -290,   104,  -290,    11,  -290,   115,   245,   250,  -290,    79,
    -290,   381,  -290,  -290,  -290,   298,   103,   103,  -290,  -290,
     103,   259,  -290,   260,   261,  -290,  -290,  -290,  -290,  -290,
     103,   263,   103,  -290,   119,   103,  -290,   121,   134,   273,
    -290,    15,  -290,  -290,  -290,    46,  -290,   280,  -290,  -290,
     173,   104,  -290,   104,  -290,  -290,   447,   104,  -290,   327,
    -290,  -290,  -290,   228,  -290,   320,   136,   215,  -290,   145,
     314,  -290,   151,  -290,   445,  -290,   447,   447,  -290,   104,
     447,  -290,   447,   455,   171,  -290,  -290,  -290,  -290,  -290,
     275,  -290,  -290,   277,   447,   178,   431,   278,  -290,   286,
    -290,   187,   287,   195,  -290,   332,  -290,  -290,   289,  -290,
    -290,  -290,   104,   104,   104,  -290,  -290,  -290,   292,   293,
     294,   296,   299,    10,   447,  -290,  -290,   301,  -290,  -290,
    -290,  -290,   104,   305,  -290,   447,   103,  -290,  -290,  -290,
     309,  -290,  -290,   103,  -290,   104,  -290,  -290,  -290,  -290,
    -290,  -290,   103,   363,   103,   311,  -290,   312,  -290,   206,
     104,  -290,    59,   474,    63,    64,    75,   104,   479,  -290,
    -290,   315,   328,  -290,  -290,   331,  -290,  -290,  -290,   333,
    -290,  -290,  -290,   215,  -290,   104,   104,    77,   339,  -290
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     2,     5,     6,     3,     4,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       1,     0,     7,    76,    69,    70,    71,    72,    75,    73,
      74,     0,    77,     0,    51,    80,    52,    78,     9,   117,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    21,
      22,    23,   127,     0,    25,     0,    27,    28,    29,    60,
       0,     0,     0,    34,    33,   100,     0,     0,   128,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    77,     0,    52,     8,     0,     0,    86,     0,    90,
       0,    98,    18,    17,     0,   120,     0,   123,    20,    24,
      26,    30,    61,    31,    32,     0,   106,   107,   101,    35,
      36,    37,     0,     0,    42,    12,     0,    48,     0,     0,
     132,   133,     0,     0,   150,   151,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    59,     0,   115,     0,     0,
     118,     0,    11,     0,    15,     0,     0,     0,   121,     0,
     111,     0,   109,   110,   113,     0,     0,     0,    40,    43,
       0,     0,    49,     0,     0,   129,   134,   123,   148,   152,
       0,     0,     0,    93,     0,     0,    96,     0,     0,     0,
     104,     0,    82,    83,    84,     0,    53,     0,    10,    88,
       0,     0,    91,     0,    99,    98,     0,     0,   124,     0,
     108,   114,   125,     0,    45,     0,     0,     0,   136,     0,
       0,   140,     0,   138,     0,    79,     0,     0,    94,     0,
       0,    97,     0,     0,     0,    62,    58,   105,    81,    85,
       0,    87,    89,     0,     0,     0,     0,     0,   112,     0,
     126,     0,     0,     0,    38,     0,   130,   137,     0,   146,
     145,   147,     0,     0,     0,   131,   141,   149,     0,     0,
       0,     0,     0,     0,     0,    65,    67,     0,    63,   116,
      14,   122,     0,     0,    19,     0,     0,    44,    46,    50,
       0,    39,   102,     0,   102,   102,   102,    92,    54,    95,
      55,    56,     0,     0,     0,     0,    57,     0,    16,     0,
       0,    13,     0,     0,     0,     0,     0,     0,     0,    64,
     119,     0,     0,   135,   103,     0,   142,   144,   143,     0,
      66,    41,    47,     0,    68,     0,   102,     0,     0,   139
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -290,  -290,  -290,  -290,   366,  -290,  -205,    93,  -290,  -290,
    -290,  -290,  -290,    -1,   -98,  -290,   152,  -290,   114,   -74,
     -11,   336,   -25,   193,  -290,   -14,  -265,  -290,   205,  -290,
    -155,   249,   189,   -21,  -289,  -290,  -290,  -166,   231,  -290,
    -290,   295,  -290,   388,   227,  -285,  -290,  -290,  -290,   270,
    -290,   186,  -290,   199,  -290,  -290,  -290,  -290,   274,  -290
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,     5,   263,    91,   133,   179,   261,
     298,   136,   182,    79,    80,   244,   245,   284,   285,    54,
      55,    56,    57,   204,   205,   209,   210,   163,   193,   194,
     196,   197,   165,   334,   322,   201,   128,   174,   175,   160,
     105,   115,   116,    64,   169,   223,    73,    89,     6,   141,
     142,   228,   229,   231,   232,   233,   274,     7,   145,   146
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint16 yytable[] =
{
      60,    61,    62,    63,    63,   156,    67,    53,   305,   221,
     214,   126,    86,   312,    88,   324,   325,   326,   323,    43,
      43,   264,     1,    87,   114,   167,    40,    93,    94,   328,
      95,    96,    97,    98,    99,   107,    43,    44,    45,    46,
      47,    58,   241,   241,    68,    85,   108,    48,    48,    41,
     102,   172,   143,   221,   188,    43,   202,   347,   301,    50,
      50,    59,    85,    66,    48,   313,   106,   211,    52,    52,
     148,   246,   140,   144,   127,    49,    50,    43,   202,   122,
     346,   161,    51,    48,   100,   101,    69,    85,    43,   134,
     154,   137,   138,   139,    70,    50,   185,   172,   152,   153,
     214,   172,   248,   166,    52,    48,    85,   177,   178,    71,
      85,    85,    43,    43,   173,   333,    48,    50,   256,   336,
     337,   140,    85,   107,    85,   144,    52,    72,    50,   180,
     181,   338,   200,   348,   191,   217,   107,    52,   107,    85,
      48,    48,    74,   203,   157,   172,   143,    75,    81,   212,
     158,   159,    50,    50,    76,   122,   272,    77,   218,   106,
     173,    52,    52,    78,   173,   222,   224,    85,    82,   225,
     195,   213,   138,   139,   192,   237,   195,   240,    83,   154,
     247,   236,    43,    84,   239,   107,   107,    85,   107,   195,
     242,    90,   107,   104,   203,   110,   252,   253,    92,   254,
     227,   266,   265,   257,   109,   273,   230,   275,   173,   111,
      48,   112,   260,   113,   107,   114,   132,    43,    44,    45,
      46,    47,    50,   218,    43,   280,   243,   287,   106,   251,
     117,    52,   286,   195,   292,   278,   279,    43,   118,   281,
     119,   282,   296,   297,   120,    48,   123,   107,   107,   107,
      90,   300,    48,   291,   124,   122,    49,    50,   304,   129,
     306,   177,   331,    51,    50,    48,    52,   107,   130,   131,
     147,   149,   286,    52,   135,   150,   151,    50,   317,   155,
     107,   162,   164,   315,   259,   320,    52,   176,   183,   184,
     187,   252,   222,   207,   134,   107,   190,   192,   195,   199,
     215,   327,   107,   222,   208,   216,   332,    43,    44,    45,
      46,    47,   260,   339,   226,   227,   230,   260,   345,   235,
     107,   107,   268,    43,    44,    45,    46,    47,   243,   250,
     262,   289,   252,   290,   294,    48,    43,    44,    45,    46,
      47,   295,   302,   299,   303,   170,    49,    50,   307,   308,
     309,    48,   310,   171,   220,   311,    52,   316,   269,   270,
     271,   318,    49,    50,    48,   321,   312,   329,   330,   147,
      42,   341,    52,    43,   170,    49,    50,    43,    44,    45,
      46,    47,   171,   258,   342,    52,   343,   103,   319,   344,
      43,    44,    45,    46,    47,   349,   288,   314,   249,   238,
     198,    48,   219,    65,   255,    48,    43,    44,    45,    46,
      47,   168,   186,    50,   234,   267,    49,    50,    48,   147,
     189,     0,   101,    51,   121,     0,    52,     0,   170,    49,
      50,   276,     0,     0,    48,     0,   171,     0,     0,    52,
      43,    44,    45,    46,    47,    49,    50,     0,     0,     0,
       0,     0,    51,   206,    43,    52,    43,    44,    45,    46,
      47,     0,     0,     0,    43,     0,     0,     0,    48,    43,
      44,    45,    46,    47,     0,     0,     0,     0,     0,    49,
      50,     0,    48,    43,    48,     0,    51,   293,    43,    52,
       0,     0,    48,     0,    50,    49,    50,    48,     0,     0,
       0,   277,    51,    52,    50,    52,     0,     0,    49,    50,
     283,    48,     0,    52,     0,   125,    48,     0,    52,     0,
       0,     0,     0,    50,     0,     0,     0,     0,    50,     0,
     335,     0,    52,     0,     0,   340,     0,    52,     8,     9,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    23,    24,    25,    26,    27,    28,    29,
      30,    31,    32,    33,    34,    35,    36,    37,     0,     0,
       0,     0,     0,     0,    38,    39,     8,     9,    10,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    27,    28,    29,    30,    31,
      32,    33,    34,    35,    36,    37
};

static const yytype_int16 yycheck[] =
{
      11,    12,    13,    14,    15,   103,    17,     8,   273,   175,
     165,    85,    33,     3,    35,   304,   305,   306,   303,     9,
       9,   226,    55,    34,    55,    56,     0,    38,    39,   314,
       3,     4,     5,     6,     7,    60,     9,    10,    11,    12,
      13,    56,   197,   198,    48,    47,    60,    37,    37,    55,
      51,   125,    54,   219,    56,     9,    10,   346,   263,    49,
      49,    55,    47,    55,    37,    55,    55,    56,    58,    58,
      95,    56,    93,    94,    85,    48,    49,     9,    10,    80,
     345,   106,    55,    37,    57,    58,    56,    47,     9,    90,
     101,    92,    52,    53,    56,    49,    56,   171,    99,   100,
     255,   175,    56,   114,    58,    37,    47,    55,    56,    56,
      47,    47,     9,     9,   125,    56,    37,    49,   216,    56,
      56,   142,    47,   148,    47,   146,    58,    47,    49,    55,
      56,    56,   153,    56,   148,    56,   161,    58,   163,    47,
      37,    37,    56,   154,    49,   219,    54,    47,    10,   163,
      55,    56,    49,    49,    56,   156,   230,    56,   169,    55,
     171,    58,    58,    56,   175,   176,   177,    47,    10,   180,
      55,    56,    52,    53,    55,    56,    55,    56,    56,   190,
     201,   192,     9,    56,   195,   210,   211,    47,   213,    55,
      56,    55,   217,    56,   205,    10,   210,   211,    55,   213,
      55,    56,   227,   217,    55,   230,    55,    56,   219,    55,
      37,    56,   223,    56,   239,    55,     8,     9,    10,    11,
      12,    13,    49,   234,     9,   239,    55,    56,    55,    56,
      55,    58,   243,    55,    56,   236,   237,     9,    56,   240,
      56,   242,    55,    56,    56,    37,    56,   272,   273,   274,
      55,    56,    37,   254,    56,   256,    48,    49,   272,    56,
     274,    55,    56,    55,    49,    37,    58,   292,    56,    56,
      55,    55,   283,    58,    56,    55,    55,    49,   292,    56,
     305,    56,    56,   284,    56,   296,    58,    55,    55,    55,
      55,   305,   303,     9,   295,   320,    58,    55,    55,    55,
      55,   312,   327,   314,    56,    55,   320,     9,    10,    11,
      12,    13,   323,   327,    55,    55,    55,   328,   343,    56,
     345,   346,     8,     9,    10,    11,    12,    13,    55,    49,
      10,    56,   346,    56,    56,    37,     9,    10,    11,    12,
      13,    55,    10,    56,    55,    47,    48,    49,    56,    56,
      56,    37,    56,    55,    56,    56,    58,    56,    44,    45,
      46,    56,    48,    49,    37,    56,     3,    56,    56,    55,
       4,    56,    58,     9,    47,    48,    49,     9,    10,    11,
      12,    13,    55,    56,    56,    58,    55,    51,   295,    56,
       9,    10,    11,    12,    13,    56,   244,   283,   205,   194,
     151,    37,   171,    15,   215,    37,     9,    10,    11,    12,
      13,   116,   142,    49,   187,   229,    48,    49,    37,    55,
     146,    -1,    58,    55,    56,    -1,    58,    -1,    47,    48,
      49,   232,    -1,    -1,    37,    -1,    55,    -1,    -1,    58,
       9,    10,    11,    12,    13,    48,    49,    -1,    -1,    -1,
      -1,    -1,    55,    56,     9,    58,     9,    10,    11,    12,
      13,    -1,    -1,    -1,     9,    -1,    -1,    -1,    37,     9,
      10,    11,    12,    13,    -1,    -1,    -1,    -1,    -1,    48,
      49,    -1,    37,     9,    37,    -1,    55,    56,     9,    58,
      -1,    -1,    37,    -1,    49,    48,    49,    37,    -1,    -1,
      -1,    56,    55,    58,    49,    58,    -1,    -1,    48,    49,
      55,    37,    -1,    58,    -1,    55,    37,    -1,    58,    -1,
      -1,    -1,    -1,    49,    -1,    -1,    -1,    -1,    49,    -1,
      56,    -1,    58,    -1,    -1,    56,    -1,    58,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    -1,    -1,
      -1,    -1,    -1,    -1,    50,    51,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    37,
      38,    39,    40,    41,    42,    43
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    55,    60,    61,    62,    63,   107,   116,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    50,    51,
       0,    55,    63,     9,    10,    11,    12,    13,    37,    48,
      49,    55,    58,    72,    78,    79,    80,    81,    56,    55,
      79,    79,    79,    79,   102,   102,    55,    79,    48,    56,
      56,    56,    47,   105,    56,    47,    56,    56,    56,    72,
      73,    10,    10,    56,    56,    47,    92,    79,    92,   106,
      55,    65,    55,    79,    79,     3,     4,     5,     6,     7,
      57,    58,    72,    80,    56,    99,    55,    81,    84,    55,
      10,    55,    56,    56,    55,   100,   101,    55,    56,    56,
      56,    56,    72,    56,    56,    55,    78,    79,    95,    56,
      56,    56,     8,    66,    72,    56,    70,    72,    52,    53,
      92,   108,   109,    54,    92,   117,   118,    55,    81,    55,
      55,    55,    72,    72,    79,    56,    73,    49,    55,    56,
      98,    81,    56,    86,    56,    91,    79,    56,   100,   103,
      47,    55,    78,    79,    96,    97,    55,    55,    56,    67,
      55,    56,    71,    55,    55,    56,   108,    55,    56,   117,
      58,    84,    55,    87,    88,    55,    89,    90,    90,    55,
      92,    94,    10,    79,    82,    83,    56,     9,    56,    84,
      85,    56,    84,    56,    89,    55,    55,    56,    79,    97,
      56,    96,    79,   104,    79,    79,    55,    55,   110,   111,
      55,   112,   113,   114,   103,    56,    79,    56,    87,    79,
      56,    89,    56,    55,    74,    75,    56,    92,    56,    82,
      49,    56,    84,    84,    84,    91,    73,    84,    56,    56,
      79,    68,    10,    64,    65,    81,    56,   110,     8,    44,
      45,    46,    78,    81,   115,    56,   112,    56,    72,    72,
      84,    72,    72,    55,    76,    77,    79,    56,    75,    56,
      56,    72,    56,    56,    56,    55,    55,    56,    69,    56,
      56,    65,    10,    55,    84,    85,    84,    56,    56,    56,
      56,    56,     3,    55,    77,    72,    56,    84,    56,    66,
      79,    56,    93,   104,    93,    93,    93,    79,   104,    56,
      56,    56,    84,    56,    92,    56,    56,    56,    56,    84,
      56,    56,    56,    55,    56,    81,    85,    93,    56,    56
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    59,    60,    60,    60,    61,    62,    62,    63,    63,
      63,    63,    63,    63,    63,    63,    63,    63,    63,    63,
      63,    63,    63,    63,    63,    63,    63,    63,    63,    63,
      63,    63,    63,    63,    63,    63,    63,    63,    64,    64,
      65,    65,    66,    66,    67,    68,    68,    69,    70,    70,
      71,    72,    72,    72,    72,    72,    72,    72,    72,    72,
      73,    73,    74,    74,    75,    76,    76,    77,    77,    78,
      78,    78,    78,    78,    79,    79,    79,    79,    80,    80,
      81,    81,    82,    82,    83,    83,    84,    84,    85,    85,
      86,    86,    87,    88,    88,    89,    90,    90,    91,    91,
      92,    92,    93,    93,    94,    94,    95,    95,    95,    96,
      96,    96,    96,    97,    97,    98,    98,    99,    99,   100,
     101,   101,   102,   103,   103,   104,   104,   105,   106,   107,
     108,   108,   108,   109,   109,   110,   111,   111,   112,   112,
     113,   113,   114,   114,   114,   115,   115,   115,   116,   117,
     117,   118,   118
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     1,     1,     1,     1,     2,     4,     3,
       6,     5,     4,     9,     8,     5,     9,     4,     4,     8,
       4,     3,     3,     3,     4,     3,     4,     3,     3,     3,
       4,     4,     4,     3,     3,     4,     4,     4,     1,     2,
       3,     9,     1,     2,     4,     0,     2,     4,     1,     2,
       4,     1,     1,     4,     7,     7,     7,     7,     5,     3,
       1,     2,     1,     2,     4,     1,     4,     1,     5,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     5,
       1,     5,     1,     1,     1,     2,     1,     4,     1,     2,
       0,     2,     4,     1,     2,     4,     1,     2,     0,     2,
       1,     2,     0,     2,     1,     2,     1,     1,     3,     1,
       1,     1,     3,     1,     2,     1,     4,     0,     2,     7,
       1,     2,     6,     0,     2,     1,     2,     1,     1,     5,
       4,     4,     1,     1,     2,     5,     1,     2,     1,    11,
       1,     2,     5,     5,     5,     1,     1,     1,     5,     4,
       1,     1,     2
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
#line 56 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_setAst(parser, (yyvsp[0].ptr)); }
#line 1680 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 3:
#line 58 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_setAst(parser, (yyvsp[0].ptr)); }
#line 1686 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 4:
#line 60 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_setAst(parser, (yyvsp[0].ptr)); }
#line 1692 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 5:
#line 65 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSmtScript((yyvsp[0].list)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1707 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 6:
#line 79 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 	
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 1721 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 7:
#line 90 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 1735 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 103 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAssertCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1750 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 9:
#line 115 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newCheckSatCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1765 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 10:
#line 127 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newCheckSatAssumCommand((yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-5]).first_line;
            (yyloc).first_column = (yylsp[-5]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1780 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 11:
#line 139 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDeclareConstCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1795 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 12:
#line 151 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newDeclareDatatypeCommand((yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1810 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 13:
#line 163 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newDeclareDatatypesCommand((yyvsp[-5].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-8]).first_line;
			(yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1825 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 14:
#line 175 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDeclareFunCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-7]).first_line;
            (yyloc).first_column = (yylsp[-7]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1840 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 15:
#line 187 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDeclareSortCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1855 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 16:
#line 199 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDefineFunsRecCommand((yyvsp[-5].list), (yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-8]).first_line;
            (yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1870 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 17:
#line 211 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDefineFunRecCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1885 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 18:
#line 223 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDefineFunCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1900 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 19:
#line 235 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDefineSortCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-7]).first_line;
            (yyloc).first_column = (yylsp[-7]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1915 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 20:
#line 247 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newEchoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1930 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 21:
#line 259 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newExitCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1945 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 22:
#line 271 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetAssertsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1960 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 23:
#line 283 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetAssignsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1975 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 24:
#line 295 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetInfoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1990 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 25:
#line 307 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetModelCommand(); 
			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[-2]).last_line;
            (yyloc).last_column = (yylsp[-2]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2004 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 26:
#line 318 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetOptionCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2019 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 27:
#line 330 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetProofCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2034 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 28:
#line 342 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetModelCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2049 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 29:
#line 354 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetUnsatCoreCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2064 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 30:
#line 366 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetValueCommand((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2079 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 31:
#line 378 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newPopCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2094 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 32:
#line 390 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newPushCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2109 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 402 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newResetAssertsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2124 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 414 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newResetCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2139 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 426 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSetInfoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2154 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 438 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSetLogicCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
            (yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2169 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 37:
#line 450 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSetOptionCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2184 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 38:
#line 464 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.list) = smt_listCreate();
			smt_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2198 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 39:
#line 475 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2212 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 40:
#line 488 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newSimpleDatatypeDeclaration((yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-2]).first_line;
			(yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2227 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 41:
#line 500 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newParametricDatatypeDeclaration((yyvsp[-5].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-8]).first_line;
			(yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2242 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 42:
#line 514 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.list) = smt_listCreate();
			smt_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2256 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 43:
#line 525 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2270 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 44:
#line 538 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newConstructorDeclaration((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2285 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 45:
#line 552 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.list) = smt_listCreate();
		}
#line 2293 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 46:
#line 557 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			} else {
				(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			}
		}
#line 2314 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 47:
#line 577 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newSelectorDeclaration((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2329 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 48:
#line 591 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.list) = smt_listCreate();
			smt_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2343 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 49:
#line 602 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2357 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 50:
#line 615 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newSortDeclaration((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2372 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 51:
#line 629 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2385 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 52:
#line 639 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2398 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 53:
#line 649 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newQualifiedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2413 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 54:
#line 661 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newLetTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2428 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 55:
#line 673 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newForallTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2443 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 56:
#line 685 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newExistsTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2458 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 57:
#line 697 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newMatchTerm((yyvsp[-4].ptr), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2473 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 58:
#line 709 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAnnotatedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2488 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 59:
#line 721 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[-1].ptr); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2503 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 60:
#line 735 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2517 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 61:
#line 746 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2531 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 62:
#line 759 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.list) = smt_listCreate();
			smt_listAdd((yyval.list), (yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2545 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 63:
#line 770 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr));
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2559 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 64:
#line 783 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newMatchCase((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2574 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 65:
#line 797 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2587 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 66:
#line 807 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newQualifiedPattern((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-3]).first_line;
			(yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2602 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 67:
#line 821 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2615 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 68:
#line 831 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newQualifiedConstructor((yyvsp[-2].ptr), (yyvsp[-1].ptr));

			(yyloc).first_line = (yylsp[-4]).first_line;
			(yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
			(yyloc).last_column = (yylsp[-1]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2630 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 69:
#line 845 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2645 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 70:
#line 857 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2660 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 71:
#line 869 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2675 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 72:
#line 881 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2690 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 73:
#line 893 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2705 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 74:
#line 907 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2720 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 75:
#line 919 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newSymbol("reset");

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2735 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 76:
#line 931 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSymbol("not"); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2750 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 77:
#line 943 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newSymbol("_");

			(yyloc).first_line = (yylsp[0]).first_line;
			(yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
			(yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2765 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 78:
#line 957 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2778 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 79:
#line 967 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newQualifiedIdentifier((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2793 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 80:
#line 981 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSimpleIdentifier1((yyvsp[0].ptr));

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2806 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 81:
#line 991 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSimpleIdentifier2((yyvsp[-2].ptr), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2821 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 82:
#line 1005 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2836 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 83:
#line 1017 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2849 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 84:
#line 1029 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2863 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 85:
#line 1040 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2877 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 86:
#line 1053 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSort1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2890 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 87:
#line 1063 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSort2((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2905 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 88:
#line 1077 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2919 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 89:
#line 1088 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2933 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 90:
#line 1101 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate();
		}
#line 2941 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 91:
#line 1106 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			} else {
				(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
			}
		}
#line 2962 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 92:
#line 1126 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newVarBinding((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2977 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 93:
#line 1140 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2991 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 94:
#line 1151 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3005 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 95:
#line 1164 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSortedVariable((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3020 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 96:
#line 1178 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3034 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 97:
#line 1189 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3048 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 98:
#line 1202 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 3054 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 99:
#line 1205 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3075 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 100:
#line 1225 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAttribute1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3090 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 101:
#line 1237 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAttribute2((yyvsp[-1].ptr), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3105 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 102:
#line 1251 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 3111 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 103:
#line 1254 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3132 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 104:
#line 1274 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3146 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 105:
#line 1285 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
        	(yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
        	(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3160 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 106:
#line 1298 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3173 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 107:
#line 1308 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3186 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 108:
#line 1318 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newCompSExpression((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3201 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 109:
#line 1332 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3214 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 110:
#line 1342 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3227 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 111:
#line 1352 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3240 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 112:
#line 1362 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newCompSExpression((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3255 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 113:
#line 1376 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3269 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 114:
#line 1387 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3283 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 115:
#line 1400 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newPropLiteral((yyvsp[0].ptr), 0); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3298 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 116:
#line 1412 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newPropLiteral((yyvsp[-1].ptr), 1); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3313 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 117:
#line 1426 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 3319 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 118:
#line 1430 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3340 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 119:
#line 1450 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3355 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 120:
#line 1464 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3369 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 121:
#line 1475 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3383 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 122:
#line 1488 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newFunctionDefinition(
				smt_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[-5]).first_line;
            (yyloc).first_column = (yylsp[-5]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3399 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 123:
#line 1503 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 3405 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 124:
#line 1506 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			if(!(yylsp[-1]).first_line) {
				(yyloc).first_line = (yylsp[0]).first_line;
            	(yyloc).first_column = (yylsp[0]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	} else {
        		(yyloc).first_line = (yylsp[-1]).first_line;
            	(yyloc).first_column = (yylsp[-1]).first_column;
				(yyloc).last_line = (yylsp[0]).last_line;
            	(yyloc).last_column = (yylsp[0]).last_column;
        	}
		}
#line 3426 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 125:
#line 1526 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3440 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 126:
#line 1537 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3454 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 127:
#line 1550 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3469 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 128:
#line 1564 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3482 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 129:
#line 1576 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newTheory((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3497 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 130:
#line 1590 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), 
				smt_newCompoundAttributeValue((yyvsp[-1].list))); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3513 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 131:
#line 1603 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), 
				smt_newCompoundAttributeValue((yyvsp[-1].list))); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3529 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 132:
#line 1616 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3542 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 133:
#line 1628 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3556 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 134:
#line 1639 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3570 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 135:
#line 1652 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSortSymbolDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3585 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 136:
#line 1666 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3599 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 137:
#line 1677 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3613 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 139:
#line 1692 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newParametricFunDeclaration((yyvsp[-7].list), (yyvsp[-4].ptr), (yyvsp[-3].list), (yyvsp[-2].list));

			(yyloc).first_line = (yylsp[-10]).first_line;
            (yyloc).first_column = (yylsp[-10]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3628 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 140:
#line 1706 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3642 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 141:
#line 1717 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column; 
		}
#line 3656 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 142:
#line 1730 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3671 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 143:
#line 1742 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newMetaSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3686 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 144:
#line 1754 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSimpleFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].list), (yyvsp[-1].list));

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3701 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 145:
#line 1768 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3716 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 146:
#line 1780 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3731 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 147:
#line 1792 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3746 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 148:
#line 1806 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newLogic((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3761 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 149:
#line 1820 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), smt_newCompoundAttributeValue((yyvsp[-1].list))); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3776 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 150:
#line 1832 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3789 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 151:
#line 1844 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3803 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 152:
#line 1855 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3817 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;


#line 3821 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
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
#line 1866 "smtlib-bison-parser.y" /* yacc.c:1906  */


int yyerror(SmtPrsr parser, const char* s) {
	smt_reportError(parser, yylloc.first_line, yylloc.first_column,
					yylloc.last_line, yylloc.last_column, s);
}
