#ifndef PARSE_SMTLIB_GLOBAL_VALUES_H
#define PARSE_SMTLIB_GLOBAL_VALUES_H

#include <string>
namespace smtlib {
    extern const std::string THEORY_CORE;

    extern const std::string SORT_BOOL;

    extern const std::string CONST_TRUE;
    extern const std::string CONST_FALSE;

    extern const std::string KW_RIGHT_ASSOC;
    extern const std::string KW_LEFT_ASSOC;
    extern const std::string KW_CHAINABLE;
    extern const std::string KW_PAIRWISE;

    extern const std::string KW_SORTS;
    extern const std::string KW_FUNS;
    extern const std::string KW_SORTS_DESC;
    extern const std::string KW_FUNS_DESC;
    extern const std::string KW_DEFINITION;

    extern const std::string KW_THEORIES;
    extern const std::string KW_LANGUAGE;
    extern const std::string KW_EXTENSIONS;
    extern const std::string KW_VALUES;
    extern const std::string KW_NOTES;

    extern const std::string KW_DIAG_OUTPUT_CHANNEL;
    extern const std::string KW_REGULAR_OUTPUT_CHANNEL;
    extern const std::string KW_RANDOM_SEED;
    extern const std::string KW_VERBOSITY;
    extern const std::string KW_REPROD_RESOURCE_LIMIT;
    extern const std::string KW_EXPAND_DEFS;
    extern const std::string KW_GLOBAL_DECLS;
    extern const std::string KW_INTERACTIVE_MODE;
    extern const std::string KW_PRINT_SUCCESS;
    extern const std::string KW_PROD_ASSERTS;
    extern const std::string KW_PROD_ASSIGNS;
    extern const std::string KW_PROD_MODELS;
    extern const std::string KW_PROD_PROOFS;
    extern const std::string KW_PROD_UNSAT_ASSUMS;
    extern const std::string KW_PROD_UNSAT_CORES;

    extern const std::string MSCONST_STRING;
    extern const std::string MSCONST_NUMERAL;
    extern const std::string MSCONST_DECIMAL;

    extern const std::string MSCONST_STRING_REF;
    extern const std::string MSCONST_NUMERAL_REF;
    extern const std::string MSCONST_DECIMAL_REF;
}

#endif //PARSE_SMTLIB_GLOBAL_VALUES_H
