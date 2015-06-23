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
    KW_CMD_ASSERT = 268,
    KW_CMD_CHK_SAT = 269,
    KW_CMD_CHK_SAT_ASSUM = 270,
    KW_CMD_DECL_CONST = 271,
    KW_CMD_DECL_FUN = 272,
    KW_CMD_DECL_SORT = 273,
    KW_CMD_DEF_FUN = 274,
    KW_CMD_DEF_FUN_REC = 275,
    KW_CMD_DEF_FUNS_REC = 276,
    KW_CMD_DEF_SORT = 277,
    KW_CMD_ECHO = 278,
    KW_CMD_EXIT = 279,
    KW_CMD_GET_ASSERTS = 280,
    KW_CMD_GET_ASSIGNS = 281,
    KW_CMD_GET_INFO = 282,
    KW_CMD_GET_MODEL = 283,
    KW_CMD_GET_OPT = 284,
    KW_CMD_GET_PROOF = 285,
    KW_CMD_GET_UNSAT_ASSUMS = 286,
    KW_CMD_GET_UNSAT_CORE = 287,
    KW_CMD_GET_VALUE = 288,
    KW_CMD_POP = 289,
    KW_CMD_PUSH = 290,
    KW_CMD_RESET = 291,
    KW_CMD_RESET_ASSERTS = 292,
    KW_CMD_SET_INFO = 293,
    KW_CMD_SET_LOGIC = 294,
    KW_CMD_SET_OPT = 295,
    META_SPEC_DECIMAL = 296,
    META_SPEC_NUMERAL = 297,
    META_SPEC_STRING = 298,
    KEYWORD = 299,
    STRING = 300,
    SYMBOL = 301,
    THEORY = 302,
    LOGIC = 303,
    KW_ATTR_SORTS = 304,
    KW_ATTR_FUNS = 305,
    KW_ATTR_THEORIES = 306
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
#define YYLAST   477

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
       0,    53,    53,    55,    57,    61,    75,    86,    99,   111,
     123,   135,   147,   159,   171,   183,   195,   207,   219,   231,
     243,   255,   267,   279,   290,   302,   314,   326,   338,   350,
     362,   374,   386,   398,   410,   422,   436,   446,   456,   468,
     480,   492,   504,   516,   530,   541,   554,   566,   578,   590,
     602,   616,   628,   640,   654,   666,   680,   692,   706,   718,
     732,   743,   756,   768,   782,   793,   807,   811,   831,   845,
     856,   869,   883,   894,   908,   910,   930,   942,   957,   959,
     979,   990,  1003,  1013,  1023,  1037,  1047,  1057,  1067,  1079,
    1090,  1103,  1115,  1130,  1133,  1153,  1167,  1178,  1191,  1207,
    1209,  1229,  1240,  1253,  1267,  1279,  1293,  1306,  1319,  1331,
    1342,  1355,  1369,  1380,  1393,  1395,  1409,  1420,  1433,  1445,
    1457,  1471,  1483,  1495,  1509,  1523,  1535,  1547,  1558
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "KW_AS", "KW_LET", "KW_FORALL",
  "KW_EXISTS", "KW_PAR", "NOT", "NUMERAL", "DECIMAL", "HEXADECIMAL",
  "BINARY", "KW_CMD_ASSERT", "KW_CMD_CHK_SAT", "KW_CMD_CHK_SAT_ASSUM",
  "KW_CMD_DECL_CONST", "KW_CMD_DECL_FUN", "KW_CMD_DECL_SORT",
  "KW_CMD_DEF_FUN", "KW_CMD_DEF_FUN_REC", "KW_CMD_DEF_FUNS_REC",
  "KW_CMD_DEF_SORT", "KW_CMD_ECHO", "KW_CMD_EXIT", "KW_CMD_GET_ASSERTS",
  "KW_CMD_GET_ASSIGNS", "KW_CMD_GET_INFO", "KW_CMD_GET_MODEL",
  "KW_CMD_GET_OPT", "KW_CMD_GET_PROOF", "KW_CMD_GET_UNSAT_ASSUMS",
  "KW_CMD_GET_UNSAT_CORE", "KW_CMD_GET_VALUE", "KW_CMD_POP", "KW_CMD_PUSH",
  "KW_CMD_RESET", "KW_CMD_RESET_ASSERTS", "KW_CMD_SET_INFO",
  "KW_CMD_SET_LOGIC", "KW_CMD_SET_OPT", "META_SPEC_DECIMAL",
  "META_SPEC_NUMERAL", "META_SPEC_STRING", "KEYWORD", "STRING", "SYMBOL",
  "THEORY", "LOGIC", "KW_ATTR_SORTS", "KW_ATTR_FUNS", "KW_ATTR_THEORIES",
  "'('", "')'", "'!'", "'_'", "$accept", "smt_file", "script",
  "command_plus", "command", "term", "term_plus", "spec_const", "symbol",
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
     305,   306,    40,    41,    33,    95
};
# endif

#define YYPACT_NINF -234

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-234)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -38,   401,    25,  -234,   -13,  -234,  -234,  -234,   353,   -11,
      -9,    91,    91,    91,    91,    91,    -7,    91,    37,    47,
      51,    75,     9,    80,    92,    85,    93,    95,   353,   141,
     144,   117,   123,   143,    91,   143,    91,    91,  -234,   437,
    -234,  -234,  -234,  -234,  -234,  -234,  -234,  -234,  -234,   236,
     128,  -234,  -234,  -234,  -234,  -234,  -234,   147,   140,   186,
     146,   152,   158,   164,   169,   170,  -234,  -234,  -234,  -234,
     175,  -234,   176,  -234,  -234,  -234,  -234,    65,   183,   184,
    -234,  -234,   361,   185,   201,  -234,   202,   112,    81,   161,
     206,   207,   208,   353,    91,   213,   353,  -234,    67,     0,
    -234,   214,  -234,   215,  -234,  -234,  -234,    91,  -234,    13,
    -234,  -234,  -234,  -234,  -234,  -234,  -234,  -234,   314,  -234,
    -234,  -234,  -234,  -234,  -234,   217,   219,  -234,  -234,   181,
     221,  -234,  -234,   -16,   220,   147,   222,   224,   224,   143,
      24,  -234,   292,  -234,   270,   226,  -234,   147,  -234,     4,
    -234,    15,   228,   231,  -234,    78,  -234,   314,  -234,  -234,
    -234,   241,   232,   240,  -234,  -234,  -234,  -234,  -234,   242,
      91,  -234,    43,    91,  -234,   105,   127,  -234,   -15,  -234,
    -234,  -234,     8,  -234,   250,  -234,  -234,    70,   147,  -234,
     147,  -234,  -234,   353,   147,  -234,   253,  -234,  -234,   161,
    -234,   137,   132,  -234,   150,  -234,   113,  -234,   353,   353,
    -234,   147,   353,  -234,   353,  -234,  -234,  -234,  -234,   254,
    -234,  -234,   255,   353,   156,   303,   256,  -234,   301,  -234,
    -234,   264,  -234,  -234,  -234,   147,   147,   147,  -234,  -234,
    -234,   265,   266,   267,   268,   274,  -234,  -234,  -234,   147,
     276,  -234,  -234,    91,  -234,   147,  -234,  -234,  -234,  -234,
    -234,  -234,   277,  -234,     5,  -234,   174,    27,    39,    45,
    -234,  -234,  -234,   279,  -234,  -234,  -234,  -234,   161,   147,
     147,    49,   280,  -234
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
      89,     0,     0,     0,   105,   110,    99,   124,   128,     0,
       0,    69,     0,     0,    72,     0,     0,    80,     0,    58,
      59,    60,     0,    38,     0,    10,    64,     0,     0,    67,
       0,    75,    74,     0,     0,   100,     0,    84,    90,     0,
     112,     0,     0,   116,     0,   114,     0,    55,     0,     0,
      70,     0,     0,    73,     0,    42,    81,    57,    61,     0,
      63,    65,     0,     0,     0,     0,     0,    88,     0,   106,
     113,     0,   122,   121,   123,     0,     0,     0,   107,   117,
     125,     0,     0,     0,     0,     0,    92,    12,    98,     0,
       0,    17,    78,     0,    78,    78,    78,    68,    39,    71,
      40,    41,     0,    14,     0,   101,     0,     0,     0,     0,
      95,   111,    79,     0,   102,   118,   120,   119,     0,     0,
      78,     0,     0,   115
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -234,  -234,  -234,  -234,   313,    10,   -86,   -67,   -10,   283,
      -8,   153,  -234,   -23,  -217,  -234,   162,  -234,  -145,   198,
     148,   -24,  -233,  -234,  -234,  -148,   189,  -234,  -234,   233,
    -234,   326,   177,  -234,  -234,  -234,  -234,   218,  -234,   151,
    -234,   149,  -234,  -234,  -234,  -234,   234,  -234
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,     5,    76,    77,    51,    52,    53,
     100,   181,   182,   186,   187,   149,   171,   172,   174,   175,
     151,   272,   264,   178,   121,   160,   161,   146,    98,   108,
     109,    61,   155,   266,    70,    86,     6,   128,   129,   200,
     201,   203,   204,   205,   237,     7,   132,   133
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint16 yytable[] =
{
      54,    57,    58,    59,    60,    60,   191,    64,    41,    83,
     142,    85,    41,   198,     1,   119,    41,   179,    50,   255,
      54,   267,   268,   269,    84,    38,    87,    88,    82,    82,
     213,   213,    41,   179,   101,   130,    46,   167,   215,    39,
      46,    54,    55,    56,    46,    63,    48,   281,   198,    82,
      48,   158,   134,    69,    48,    94,    99,   188,   271,    95,
      46,   217,   280,   127,   131,   107,   153,   173,   190,    54,
      48,    82,   120,    41,    42,    43,    44,    45,    41,   191,
     275,   135,    65,    82,   140,    54,    41,   115,    54,    82,
     158,   147,   276,    82,   158,   170,   209,   152,   277,    41,
      66,    46,   282,   139,    67,   127,    46,   225,   159,   131,
      47,    48,   169,   143,    46,   177,    48,    49,   114,   144,
     145,    41,    99,   220,    48,    82,   189,    46,    68,   158,
     180,   194,   130,    71,    54,   235,    72,    48,    73,   231,
      41,    42,    43,    44,    45,   195,    74,   159,    75,    46,
      78,   159,   115,    79,   216,    41,    82,   173,   212,    48,
     208,   125,   126,   211,   221,   222,   240,   223,    46,    41,
      80,   226,   180,   232,   233,   234,    81,    47,    48,   173,
     214,    97,    41,    46,   134,    54,   159,    82,   243,   199,
     229,   228,   102,    48,   236,   103,   195,    46,   104,    99,
      54,    54,   202,   238,    54,   105,    54,    48,   173,   249,
      46,   106,   254,   134,   256,    54,   107,    54,   241,   242,
      48,   110,   244,   111,   245,    82,   262,   273,   112,   113,
     125,   126,   221,   248,   164,   115,   116,   117,   122,    89,
      90,    91,    92,   265,    41,    42,    43,    44,    45,    41,
      42,    43,    44,    45,   123,   124,   274,   221,   136,   137,
     138,    41,    42,    43,    44,    45,   141,   148,   150,   162,
     279,   163,    46,   166,   170,    94,   173,    46,   184,   185,
     192,    47,    48,   193,   199,   156,    47,    48,    49,    46,
      93,    94,   202,   157,   197,   207,   219,   156,    47,    48,
      41,    42,    43,    44,    45,   157,   227,   246,   247,   251,
     252,    41,    42,    43,    44,    45,   253,    40,   257,   258,
     259,   260,    41,    42,    43,    44,    45,   261,    46,   263,
     270,   278,    96,   283,   210,   218,   176,    47,    48,    46,
     224,    62,   154,   206,    49,   183,   196,   165,    47,    48,
      46,     0,   230,   239,     0,    49,   250,     0,   156,    47,
      48,    41,    42,    43,    44,    45,   157,   168,     0,    41,
      42,    43,    44,    45,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    46,
       0,     0,     0,     0,     0,     0,     0,    46,    47,    48,
       0,     0,     0,     0,     0,    49,    47,    48,     0,     0,
       0,     0,     0,   118,     8,     9,    10,    11,    12,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    29,    30,    31,    32,    33,
      34,    35,     0,     0,     0,     0,     0,     0,    36,    37,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    34,    35
};

static const yytype_int16 yycheck[] =
{
       8,    11,    12,    13,    14,    15,   151,    17,     8,    33,
      96,    35,     8,   161,    52,    82,     8,     9,     8,   236,
      28,   254,   255,   256,    34,     0,    36,    37,    44,    44,
     175,   176,     8,     9,    57,    51,    36,    53,    53,    52,
      36,    49,    53,    52,    36,    52,    46,   280,   196,    44,
      46,   118,    52,    44,    46,    55,    52,    53,    53,    49,
      36,    53,   279,    87,    88,    52,    53,    52,    53,    77,
      46,    44,    82,     8,     9,    10,    11,    12,     8,   224,
      53,    89,    45,    44,    94,    93,     8,    77,    96,    44,
     157,    99,    53,    44,   161,    52,    53,   107,    53,     8,
      53,    36,    53,    93,    53,   129,    36,   193,   118,   133,
      45,    46,   135,    46,    36,   139,    46,    52,    53,    52,
      53,     8,    52,    53,    46,    44,   149,    36,    53,   196,
     140,    53,    51,    53,   142,   202,    44,    46,    53,     7,
       8,     9,    10,    11,    12,   155,    53,   157,    53,    36,
       9,   161,   142,     9,   178,     8,    44,    52,    53,    46,
     170,    49,    50,   173,   187,   188,    53,   190,    36,     8,
      53,   194,   182,    41,    42,    43,    53,    45,    46,    52,
      53,    53,     8,    36,    52,   193,   196,    44,   211,    52,
      53,   199,    52,    46,   202,     9,   206,    36,    52,    52,
     208,   209,    52,    53,   212,    53,   214,    46,    52,    53,
      36,    53,   235,    52,   237,   223,    52,   225,   208,   209,
      46,    52,   212,    53,   214,    44,   249,    53,    53,    53,
      49,    50,   255,   223,    53,   225,    53,    53,    53,     3,
       4,     5,     6,   253,     8,     9,    10,    11,    12,     8,
       9,    10,    11,    12,    53,    53,   266,   280,    52,    52,
      52,     8,     9,    10,    11,    12,    53,    53,    53,    52,
     278,    52,    36,    52,    52,    55,    52,    36,     8,    53,
      52,    45,    46,    52,    52,    44,    45,    46,    52,    36,
      54,    55,    52,    52,    53,    53,    46,    44,    45,    46,
       8,     9,    10,    11,    12,    52,    53,    53,    53,    53,
       9,     8,     9,    10,    11,    12,    52,     4,    53,    53,
      53,    53,     8,     9,    10,    11,    12,    53,    36,    53,
      53,    52,    49,    53,   172,   182,   138,    45,    46,    36,
     192,    15,   109,   166,    52,    53,   157,   129,    45,    46,
      36,    -1,   201,   204,    -1,    52,    53,    -1,    44,    45,
      46,     8,     9,    10,    11,    12,    52,   133,    -1,     8,
       9,    10,    11,    12,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    36,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    36,    45,    46,
      -1,    -1,    -1,    -1,    -1,    52,    45,    46,    -1,    -1,
      -1,    -1,    -1,    52,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    22,    23,    24,    25,    26,    27,    28,
      29,    30,    31,    32,    33,    34,    35,    36,    37,    38,
      39,    40,    -1,    -1,    -1,    -1,    -1,    -1,    47,    48,
      13,    14,    15,    16,    17,    18,    19,    20,    21,    22,
      23,    24,    25,    26,    27,    28,    29,    30,    31,    32,
      33,    34,    35,    36,    37,    38,    39,    40
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
      95,    96,    52,    97,    98,    99,    88,    53,    64,    53,
      72,    64,    53,    74,    53,    53,    77,    53,    67,    46,
      53,    69,    69,    69,    76,    62,    69,    53,    66,    53,
      95,     7,    41,    42,    43,    63,    66,   100,    53,    97,
      53,    61,    61,    69,    61,    61,    53,    53,    61,    53,
      53,    53,     9,    52,    69,    70,    69,    53,    53,    53,
      53,    53,    69,    53,    78,    64,    89,    78,    78,    78,
      53,    53,    77,    53,    64,    53,    53,    53,    52,    66,
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
#line 1620 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 3:
#line 55 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_setAst(parser, (yyvsp[0].ptr)); }
#line 1626 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 4:
#line 57 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.ptr) = (yyvsp[0].ptr); smt_setAst(parser, (yyvsp[0].ptr)); }
#line 1632 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 5:
#line 62 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSmtScript((yyvsp[0].list)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1647 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 6:
#line 76 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 	
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 1661 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 7:
#line 87 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 1675 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 100 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAssertCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1690 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 9:
#line 112 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newCheckSatCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1705 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 10:
#line 124 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newCheckSatAssumCommand((yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-5]).first_line;
            (yyloc).first_column = (yylsp[-5]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1720 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 11:
#line 136 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDeclareConstCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1735 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 12:
#line 148 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDeclareFunCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-7]).first_line;
            (yyloc).first_column = (yylsp[-7]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1750 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 13:
#line 160 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDeclareSortCommand((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1765 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 14:
#line 172 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDefineFunsRecCommand((yyvsp[-5].list), (yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-8]).first_line;
            (yyloc).first_column = (yylsp[-8]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1780 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 15:
#line 184 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDefineFunRecCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1795 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 16:
#line 196 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDefineFunCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1810 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 17:
#line 208 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newDefineSortCommand((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-7]).first_line;
            (yyloc).first_column = (yylsp[-7]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1825 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 18:
#line 220 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newEchoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1840 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 19:
#line 232 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newExitCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1855 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 20:
#line 244 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetAssertsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1870 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 21:
#line 256 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetAssignsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1885 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 22:
#line 268 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetInfoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1900 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 23:
#line 280 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetModelCommand(); 
			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[-2]).last_line;
            (yyloc).last_column = (yylsp[-2]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1914 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 24:
#line 291 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetOptionCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1929 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 25:
#line 303 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetProofCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1944 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 26:
#line 315 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetModelCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1959 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 27:
#line 327 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetUnsatCoreCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1974 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 28:
#line 339 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newGetValueCommand((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 1989 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 29:
#line 351 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newPopCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2004 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 30:
#line 363 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newPushCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2019 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 31:
#line 375 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newResetAssertsCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2034 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 32:
#line 387 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newResetCommand(); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2049 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 399 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSetInfoCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2064 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 411 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSetLogicCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
            (yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2079 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 423 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSetOptionCommand((yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2094 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 437 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2107 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 37:
#line 447 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2120 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 38:
#line 457 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newQualifiedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2135 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 39:
#line 469 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newLetTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2150 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 40:
#line 481 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newForallTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2165 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 41:
#line 493 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newExistsTerm((yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[-3]).last_line;
            (yyloc).last_column = (yylsp[-3]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2180 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 42:
#line 505 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAnnotatedTerm((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2195 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 43:
#line 517 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[-1].ptr); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2210 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 44:
#line 531 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2224 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 45:
#line 542 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2238 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 46:
#line 555 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2253 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 47:
#line 567 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2268 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 48:
#line 579 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2283 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 49:
#line 591 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2298 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 50:
#line 603 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2313 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 51:
#line 617 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = (yyvsp[0].ptr);

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2328 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 52:
#line 629 "smtlib-bison-parser.y" /* yacc.c:1646  */
    {
			(yyval.ptr) = smt_newSymbol("reset");

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2343 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 53:
#line 641 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSymbol("not"); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2358 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 54:
#line 655 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2373 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 55:
#line 667 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newQualifiedIdentifier((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2388 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 56:
#line 681 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newIdentifier1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2403 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 57:
#line 693 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newIdentifier2((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2418 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 58:
#line 707 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2433 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 59:
#line 719 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2448 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 60:
#line 733 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2462 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 61:
#line 744 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2476 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 62:
#line 757 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSort1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2491 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 63:
#line 769 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSort2((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

			smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2506 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 64:
#line 783 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2520 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 65:
#line 794 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2534 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 66:
#line 807 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate();
		}
#line 2542 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 67:
#line 812 "smtlib-bison-parser.y" /* yacc.c:1646  */
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
#line 2563 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 68:
#line 832 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newVarBinding((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2578 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 69:
#line 846 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2592 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 70:
#line 857 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2606 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 71:
#line 870 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSortedVariable((yyvsp[-2].ptr), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[-1]).last_line;
            (yyloc).last_column = (yylsp[-1]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2621 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 72:
#line 884 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2635 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 73:
#line 895 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2649 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 74:
#line 908 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 2655 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 75:
#line 911 "smtlib-bison-parser.y" /* yacc.c:1646  */
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
#line 2676 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 76:
#line 931 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAttribute1((yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2691 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 77:
#line 943 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAttribute2((yyvsp[-1].ptr), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2706 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 78:
#line 957 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 2712 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 79:
#line 960 "smtlib-bison-parser.y" /* yacc.c:1646  */
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
#line 2733 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 80:
#line 980 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2747 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 81:
#line 991 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
        	(yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
        	(yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2761 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 82:
#line 1004 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2774 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 83:
#line 1014 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2787 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 84:
#line 1024 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newCompSExpression((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2802 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 85:
#line 1038 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2815 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 86:
#line 1048 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2828 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 87:
#line 1058 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2841 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 88:
#line 1068 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newCompSExpression((yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-2]).first_line;
            (yyloc).first_column = (yylsp[-2]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2854 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 89:
#line 1080 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2868 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 90:
#line 1091 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2882 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 91:
#line 1104 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newPropLiteral((yyvsp[0].ptr), 0); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2897 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 92:
#line 1116 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newPropLiteral((yyvsp[-1].ptr), 1); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2912 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 93:
#line 1130 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 2918 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 94:
#line 1134 "smtlib-bison-parser.y" /* yacc.c:1646  */
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
#line 2939 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 95:
#line 1154 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)); 

			(yyloc).first_line = (yylsp[-6]).first_line;
            (yyloc).first_column = (yylsp[-6]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2954 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 96:
#line 1168 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2968 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 97:
#line 1179 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 2982 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 98:
#line 1192 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newFunctionDefinition(
				smt_newFunctionDeclaration((yyvsp[-5].ptr), (yyvsp[-3].list), (yyvsp[-1].ptr)), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[-5]).first_line;
            (yyloc).first_column = (yylsp[-5]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 2998 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 99:
#line 1207 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { (yyval.list) = smt_listCreate(); }
#line 3004 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 100:
#line 1210 "smtlib-bison-parser.y" /* yacc.c:1646  */
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
#line 3025 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 101:
#line 1230 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3039 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 102:
#line 1241 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3053 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 103:
#line 1254 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3068 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 104:
#line 1268 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3081 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 105:
#line 1280 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newTheory((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3096 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 106:
#line 1294 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), 
				smt_newCompoundAttributeValue((yyvsp[-1].list))); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3112 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 107:
#line 1307 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), 
				smt_newCompoundAttributeValue((yyvsp[-1].list))); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3128 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 108:
#line 1320 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3141 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 109:
#line 1332 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3155 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 110:
#line 1343 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3169 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 111:
#line 1356 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSortSymbolDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3184 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 112:
#line 1370 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3198 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 113:
#line 1381 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3212 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 115:
#line 1396 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newParamFunDeclaration((yyvsp[-7].list), (yyvsp[-4].ptr), (yyvsp[-3].list), (yyvsp[-2].list)); 

			(yyloc).first_line = (yylsp[-10]).first_line;
            (yyloc).first_column = (yylsp[-10]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3227 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 116:
#line 1410 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3241 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 117:
#line 1421 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list);

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column; 
		}
#line 3255 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 118:
#line 1434 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3270 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 119:
#line 1446 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newMetaSpecConstFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3285 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 120:
#line 1458 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newIdentifFunDeclaration((yyvsp[-3].ptr), (yyvsp[-2].list), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3300 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 121:
#line 1472 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3315 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 122:
#line 1484 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3330 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 123:
#line 1496 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3345 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 124:
#line 1510 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newLogic((yyvsp[-2].ptr), (yyvsp[-1].list)); 

			(yyloc).first_line = (yylsp[-4]).first_line;
            (yyloc).first_column = (yylsp[-4]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3360 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 125:
#line 1524 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = smt_newAttribute2((yyvsp[-3].ptr), smt_newCompoundAttributeValue((yyvsp[-1].list))); 

			(yyloc).first_line = (yylsp[-3]).first_line;
            (yyloc).first_column = (yylsp[-3]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;

            smt_setLocation(parser, (yyval.ptr), (yyloc).first_line, (yyloc).first_column, (yyloc).last_line, (yyloc).last_column);
		}
#line 3375 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 126:
#line 1536 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.ptr) = (yyvsp[0].ptr); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3388 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 127:
#line 1548 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			(yyval.list) = smt_listCreate(); 
			smt_listAdd((yyval.list), (yyvsp[0].ptr)); 

			(yyloc).first_line = (yylsp[0]).first_line;
            (yyloc).first_column = (yylsp[0]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3402 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;

  case 128:
#line 1559 "smtlib-bison-parser.y" /* yacc.c:1646  */
    { 
			smt_listAdd((yyvsp[-1].list), (yyvsp[0].ptr)); 
			(yyval.list) = (yyvsp[-1].list); 

			(yyloc).first_line = (yylsp[-1]).first_line;
            (yyloc).first_column = (yylsp[-1]).first_column;
			(yyloc).last_line = (yylsp[0]).last_line;
            (yyloc).last_column = (yylsp[0]).last_column;
		}
#line 3416 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
    break;


#line 3420 "smtlib-bison-parser.tab.c" /* yacc.c:1646  */
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
#line 1570 "smtlib-bison-parser.y" /* yacc.c:1906  */


int yyerror(SmtPrsr parser, const char *s) {
	smt_reportError(parser, yylloc.first_line, yylloc.first_column,
					yylloc.last_line, yylloc.last_column, s);
}
