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
        static std::string buildTheoryUnloadable(std::string theory);

        static std::string buildTheoryUnknown(std::string theory);

        static std::string buildTheoryAlreadyLoaded(std::string theory);

        static std::string buildLogicUnloadable(std::string logic);

        static std::string buildLogicUnknown(std::string logic);

        static std::string buildLogicAlreadySet(std::string logic);


        static std::string buildSortUnknown(std::string name, int rowLeft, int colLeft, int rowRight, int colRight);

        static std::string buildSortArity(std::string name, unsigned long arity, unsigned long argCount,
                                          int rowLeft, int colLeft, int rowRight, int colRight);

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
    };
}

#endif //PARSE_SMTLIB_ERROR_MESSAGES_H
