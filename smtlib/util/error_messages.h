#ifndef PARSE_SMTLIB_ERROR_MESSAGES_H
#define PARSE_SMTLIB_ERROR_MESSAGES_H

#include <string>
#include <sstream>
#include <vector>

namespace smtlib {
    class ErrorMessages {
    private:
        static std::string extractFirstN(std::string str, unsigned long n);

        static void printArray(std::stringstream &ss,
                               std::vector<std::string> &array,
                               std::string separator);

    public:
        static const std::string ERR_NULL_NODE_VISIT;
        static const std::string ERR_ATTR_MISSING_KEYWORD;
        static const std::string ERR_SYMBOL_MALFORMED;
        static const std::string ERR_KEYWORD_MALFORMED;
        static const std::string ERR_PROP_LIT_MISSING_SYMBOL;
        static const std::string ERR_ASSERT_MISSING_TERM;
        static const std::string ERR_DECL_CONST_MISSING_NAME;
        static const std::string ERR_DECL_CONST_MISSING_SORT;
        static const std::string ERR_DECL_DATATYPE_MISSING_NAME;
        static const std::string ERR_DECL_DATATYPE_MISSING_DECL;
        static const std::string ERR_DECL_DATATYPES_MISSING_SORTS;
        static const std::string ERR_DECL_DATATYPES_MISSING_DECLS;
        static const std::string ERR_DECL_FUN_MISSING_NAME;
        static const std::string ERR_DECL_FUN_MISSING_RET;
        static const std::string ERR_DECL_SORT_MISSING_NAME;
        static const std::string ERR_DECL_SORT_MISSING_ARITY;
        static const std::string ERR_DEF_FUN_MISSING_DEF;
        static const std::string ERR_DEF_FUN_REC_MISSING_DEF;
        static const std::string ERR_DEF_FUNS_REC_EMPTY_DECLS;
        static const std::string ERR_DEF_FUNS_REC_EMPTY_BODIES;
        static const std::string ERR_DEF_SORT_MISSING_NAME;
        static const std::string ERR_DEF_SORT_MISSING_DEF;
        static const std::string ERR_ECHO_EMPTY_STRING;
        static const std::string ERR_GET_INFO_MISSING_FLAG;
        static const std::string ERR_GET_OPT_MISSING_OPT;
        static const std::string ERR_GET_VALUE_EMPTY_TERMS;
        static const std::string ERR_POP_MISSING_NUMERAL;
        static const std::string ERR_PUSH_MISSING_NUMERAL;
        static const std::string ERR_SET_INFO_MISSING_INFO;
        static const std::string ERR_SET_LOGIC_MISSING_LOGIC;
        static const std::string ERR_SET_OPT_MISSING_OPT;
        static const std::string ERR_OPT_VALUE_STRING;
        static const std::string ERR_OPT_VALUE_NUMERAL;
        static const std::string ERR_OPT_VALUE_BOOLEAN;
        static const std::string ERR_FUN_DECL_MISSING_NAME;
        static const std::string ERR_FUN_DECL_MISSING_RET;
        static const std::string ERR_FUN_DEF_MISSING_SIG;
        static const std::string ERR_FUN_DEF_MISSING_BODY;
        static const std::string ERR_ID_MISSING_SYMBOL;
        static const std::string ERR_ID_EMPTY_INDICES;
        static const std::string ERR_QUAL_ID_MISSING_ID;
        static const std::string ERR_QUAL_ID_MISSING_SORT;
        static const std::string ERR_LOGIC_MISSING_NAME;
        static const std::string ERR_LOGIC_EMPTY_ATTRS;
        static const std::string ERR_THEORY_MISSING_NAME;
        static const std::string ERR_THEORY_EMPTY_ATTRS;
        static const std::string ERR_ATTR_VALUE_STRING;
        static const std::string ERR_ATTR_VALUE_SORTS;
        static const std::string ERR_ATTR_VALUE_SORTS_EMPTY;
        static const std::string ERR_ATTR_VALUE_FUNS;
        static const std::string ERR_ATTR_VALUE_FUNS_EMPTY;
        static const std::string ERR_ATTR_VALUE_THEORIES;
        static const std::string ERR_ATTR_VALUE_THEORIES_EMPTY;
        static const std::string ERR_SORT_MISSING_ID;
        static const std::string ERR_SORT_EMPTY_ARGS;
        static const std::string ERR_SORT_SYM_DECL_MISSING_ID;
        static const std::string ERR_SORT_SYM_DECL_MISSING_ARITY;
        static const std::string ERR_SPEC_CONST_DECL_MISSING_CONST;
        static const std::string ERR_SPEC_CONST_DECL_MISSING_SORT;
        static const std::string ERR_META_SPEC_CONST_DECL_MISSING_CONST;
        static const std::string ERR_META_SPEC_CONST_DECL_MISSING_SORT;
        static const std::string ERR_FUN_SYM_DECL_MISSING_ID;
        static const std::string ERR_FUN_SYM_DECL_EMPTY_SIG;
        static const std::string ERR_PARAM_FUN_SYM_DECL_EMPTY_PARAMS;
        static const std::string ERR_PARAM_FUN_SYM_DECL_MISSING_ID;
        static const std::string ERR_PARAM_FUN_SYM_DECL_EMPTY_SIG;
        static const std::string ERR_SORT_DECL_MISSING_SYMBOL;
        static const std::string ERR_SORT_DECL_MISSING_ARITY;
        static const std::string ERR_SEL_DECL_MISSING_SYMBOL;
        static const std::string ERR_SEL_DECL_MISSING_SORT;
        static const std::string ERR_CONS_DECL_MISSING_SYMBOL;
        static const std::string ERR_DATATYPE_DECL_EMPTY_CONS;
        static const std::string ERR_PARAM_DATATYPE_DECL_EMPTY_PARAMS;
        static const std::string ERR_PARAM_DATATYPE_DECL_EMPTY_CONS;
        static const std::string ERR_QUAL_CONS_MISSING_SYMBOL;
        static const std::string ERR_QUAL_CONS_MISSING_SORT;
        static const std::string ERR_QUAL_PATTERN_MISSING_CONS;
        static const std::string ERR_QUAL_PATTERN_EMPTY_SYMS;
        static const std::string ERR_MATCH_CASE_MISSING_PATTERN;
        static const std::string ERR_MATCH_CASE_MISSING_TERM;
        static const std::string ERR_QUAL_TERM_MISSING_ID;
        static const std::string ERR_QUAL_TERM_EMPTY_TERMS;
        static const std::string ERR_LET_TERM_MISSING_TERM;
        static const std::string ERR_LET_TERM_EMPTY_VARS;
        static const std::string ERR_FORALL_TERM_MISSING_TERM;
        static const std::string ERR_FORALL_TERM_EMPTY_VARS;
        static const std::string ERR_EXISTS_TERM_MISSING_TERM;
        static const std::string ERR_EXISTS_TERM_EMPTY_VARS;
        static const std::string ERR_MATCH_TERM_MISSING_TERM;
        static const std::string ERR_MATCH_TERM_EMPTY_CASES;
        static const std::string ERR_ANNOT_TERM_MISSING_TERM;
        static const std::string ERR_ANNOT_TERM_EMPTY_ATTRS;
        static const std::string ERR_SORTED_VAR_MISSING_SYMBOL;
        static const std::string ERR_SORTED_VAR_MISSING_SORT;
        static const std::string ERR_VAR_BIND_MISSING_SYMBOL;
        static const std::string ERR_VAR_BIND_MISSING_SORT;

        static std::string buildTheoryUnloadable(std::string theory);

        static std::string buildTheoryUnknown(std::string theory);

        static std::string buildTheoryAlreadyLoaded(std::string theory);

        static std::string buildLogicUnloadable(std::string logic);

        static std::string buildLogicUnknown(std::string logic);

        static std::string buildLogicAlreadySet(std::string logic);


        static std::string buildSortUnknown(std::string name, int rowLeft, int colLeft, int rowRight, int colRight);

        static std::string buildSortArity(std::string name, unsigned long arity, unsigned long argCount,
                                          int rowLeft, int colLeft, int rowRight, int colRight);

        static std::string buildSortParamArity(std::string sort, std::string sortName);

        static std::string buildAssertTermNotWellSorted(std::string term,
                                                        int rowLeft, int colLeft, int rowRight, int colRight);

        static std::string buildAssertTermNotBool(std::string term, std::string termSort,
                                                  int rowLeft, int colLeft, int rowRight, int colRight);

        static std::string buildConstAlreadyExists(std::string name);

        static std::string buildConstUnknown(std::string name);

        static std::string buildConstMultipleSorts(std::string name,
                                                   std::vector<std::string> &possibleSorts);

        static std::string buildConstWrongSort(std::string name,
                                               std::string wrongSort,
                                               std::vector<std::string> &possibleSorts);

        static std::string buildFunAlreadyExists(std::string name);

        static std::string buildFunBodyWrongSort(std::string body, std::string wrongSort, std::string rightSort,
                                                 int rowLeft, int colLeft, int rowRight, int colRight);

        static std::string buildFunBodyWrongSort(std::string name, std::string body,
                                                 std::string wrongSort, std::string rightSort,
                                                 int rowLeft, int colLeft, int rowRight, int colRight);

        static std::string buildFunBodyNotWellSorted(std::string body, int rowLeft,
                                                     int colLeft, int rowRight, int colRight);

        static std::string buildFunBodyNotWellSorted(std::string name, std::string body, int rowLeft,
                                                     int colLeft, int rowRight, int colRight);

        static std::string buildSortAlreadyExists(std::string name);

        static std::string buildSpecConstAlreadyExists(std::string name);

        static std::string buildMetaSpecConstAlreadyExists(std::string name);

        static std::string buildRightAssocParamCount(std::string name);

        static std::string buildRightAssocRetSort(std::string name);

        static std::string buildLeftAssocParamCount(std::string name);

        static std::string buildLeftAssocRetSort(std::string name);

        static std::string buildChainableAndPairwise(std::string name);

        static std::string buildChainableParamCount(std::string name);

        static std::string buildChainableParamSort(std::string name);

        static std::string buildChainableRetSort(std::string name);

        static std::string buildPairwiseParamCount(std::string name);

        static std::string buildPairwiseParamSort(std::string name);

        static std::string buildPairwiseRetSort(std::string name);

        static std::string buildTermNotWellSorted(std::string term, int rowLeft,
                                                  int colLeft, int rowRight, int colRight);

        static std::string buildStackUnpoppable(unsigned long levels);

        static std::string buildLiteralUnknownSort(std::string literalType);

        static std::string buildLiteralMultipleSorts(std::string literalType,
                                                     std::vector<std::string> &possibleSorts);

        static std::string buildFunUnknownDecl(std::string name,
                                               std::string retSort);

        static std::string buildFunUnknownDecl(std::string name,
                                               unsigned long paramCount,
                                               std::string retSort);

        static std::string buildFunUnknownDecl(std::string name,
                                               std::vector<std::string> argSorts);

        static std::string buildFunUnknownDecl(std::string name,
                                               std::vector<std::string> argSorts,
                                               std::string retSort);

        static std::string buildFunMultipleDecls(std::string name,
                                                 unsigned long paramCount,
                                                 std::string retSort);

        static std::string buildFunMultipleDecls(std::string name,
                                                 std::vector<std::string> argSorts,
                                                 std::vector<std::string> retSorts);

        static std::string buildQuantTermWrongSort(std::string term, std::string wrongSort, std::string rightSort,
                                                   int rowLeft, int colLeft, int rowRight, int colRight);

        static std::string buildPatternMismatch(std::string sort, std::string pattern);

        static std::string buildCasesMismatch(std::vector<std::string> caseSorts);

        static std::string buildParamFunDeclUnusedSortParams(std::vector<std::string> unusedParams);

        static std::string buildParamDatatypeDeclUnusedSortParams(std::vector<std::string> unusedParams);

        static std::string buildSortDefUnusedSortParams(std::vector<std::string> unusedParams);

        static std::string buildAttrValueSortDecl(std::string attrValue);

        static std::string buildAttrValueFunDecl(std::string attrValue);

        static std::string buildAttrValueSymbol(std::string attrValue);

        static std::string buildDeclDatatypesCount(unsigned long sortDeclCount,
                                                   unsigned long datatypeDeclCount);

        static std::string buildDeclDatatypeArity(std::string name, unsigned long arity,
                                                  unsigned long paramCount);

        static std::string buildDefFunsRecCount(unsigned long declCount,
                                                unsigned long bodyCount);
    };
}

#endif //PARSE_SMTLIB_ERROR_MESSAGES_H
