#include "error_messages.h"

using namespace std;
using namespace smtlib;

string ErrorMessages::extractFirstN(string str, unsigned long n) {
    if (str.length() > n)
        return string(str, 0, n) + "[...]";
    else
        return str;
}

void ErrorMessages::printArray(std::stringstream &ss,
                               std::vector<std::string> &array,
                               std::string separator) {
    bool first = true;
    for (auto it = array.begin(); it != array.end(); it++) {
        if (first) {
            first = false;
        } else {
            ss << separator;
        }
        ss << (*it);
    }
}

string ErrorMessages::buildTheoryUnloadable(string theory) {
    return "Cannot load theory '" + theory + "'";
}

string ErrorMessages::buildLogicUnloadable(string logic) {
    return "Cannot load logic '" + logic + "'";
}

string ErrorMessages::buildTheoryUnknown(string theory) {
    return "Unknown theory '" + theory + "'";
}

string ErrorMessages::buildLogicUnknown(string logic) {
    return "Unknown logic '" + logic + "'";
}

string ErrorMessages::buildSortUnknown(string name, int rowLeft, int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "Unknown sort '" << name << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    return ss.str();
}

string ErrorMessages::buildSortArity(string name, unsigned long arity, unsigned long argCount,
                                     int rowLeft, int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "Sort '" << name << "' should have " << arity << " arguments, not " << argCount;

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    return ss.str();
}

string ErrorMessages::buildAssertTermNotWellSorted(string term,
                                                   int rowLeft, int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "Assertion term '" << extractFirstN(term, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is not well-sorted";
    return ss.str();
}

string ErrorMessages::buildAssertTermNotBool(string term, string termSort,
                                             int rowLeft, int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "Assertion term '" << extractFirstN(term, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is of type " << termSort << ", not Bool";
    return ss.str();
}

string ErrorMessages::buildConstAlreadyExists(string name) {
    return "Constant '" + name + "' already exists with same sort";
}

string ErrorMessages::buildConstUnknown(string name) {
    return "Unknown constant '" + name + "'";
}

string ErrorMessages::buildFunAlreadyExists(string name) {
    return "Function '" + name + "' already exists with the same signature";
}

string ErrorMessages::buildSortAlreadyExists(string name) {
    return "Sort symbol '" + name + "' already exists";
}

string ErrorMessages::buildSpecConstAlreadyExists(string name) {
    return "Specification constant '" + name + "' already exists";
}

string ErrorMessages::buildMetaSpecConstAlreadyExists(string name) {
    return "Sort for meta specification constant '" + name + "' already declared";
}

string ErrorMessages::buildRightAssocParamCount(string name) {
    return "Function '" + name +
           "' cannot be right associative - it does not have 2 parameters";
}

string ErrorMessages::buildRightAssocRetSort(string name) {
    return "Function '" + name +
           "' cannot be right associative - sort of second parameter not the same as return sort";
}

string ErrorMessages::buildLeftAssocParamCount(string name) {
    return "Function '" + name +
           "' cannot be left associative - it does not have 2 parameters";
}

string ErrorMessages::buildLeftAssocRetSort(string name) {
    return "Function '" + name +
           "' cannot be left associative - sort of first parameter not the same as return sort";
}

string ErrorMessages::buildChainableAndPairwise(string name) {
    return "Function '" + name +
           "' cannot be both chainable and pairwise";
}

string ErrorMessages::buildChainableParamCount(string name) {
    return "Function '" + name +
           "' cannot be chainable - it does not have 2 parameters";
}

string ErrorMessages::buildChainableParamSort(string name) {
    return "Function '" + name + "' cannot be chainable " + "- parameters do not have the same sort";
}

string ErrorMessages::buildChainableRetSort(string name) {
    return "Function '" + name + "' cannot be chainable " + "- return sort is not Bool";
}

string ErrorMessages::buildPairwiseParamCount(string name) {
    return "Function '" + name +
           "' cannot be chainable - it does not have 2 parameters";
}

string ErrorMessages::buildPairwiseParamSort(string name) {
    return "Function '" + name + "' cannot be pairwise " + "- parameters do not have the same sort";
}

string ErrorMessages::buildPairwiseRetSort(string name) {
    return "Function '" + name + "' cannot be pairwise " + "- return sort is not Bool";
}

string ErrorMessages::buildFunBodyWrongSort(string body, string wrongSort, string rightSort,
                                            int rowLeft, int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "Function body '" << extractFirstN(body, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is of type " << wrongSort << ", not " << rightSort;
    return ss.str();
}

string ErrorMessages::buildFunBodyWrongSort(string name, string body,
                                            string wrongSort, string rightSort,
                                            int rowLeft, int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "The body of function " << name << ", '" << extractFirstN(body, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is of type " << wrongSort << ", not " << rightSort;
    return ss.str();
}

string ErrorMessages::buildFunBodyNotWellSorted(string body,
                                                int rowLeft, int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "Function body '" << extractFirstN(body, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is not well-sorted";
    return ss.str();
}

string ErrorMessages::buildFunBodyNotWellSorted(string name, string body, int rowLeft,
                                                int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "The body of function '" << name << "', '" << extractFirstN(body, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is not well-sorted";
    return ss.str();
}

string ErrorMessages::buildTermNotWellSorted(string term, int rowLeft,
                                             int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "Term '" << extractFirstN(term, 50) << "'";

    if (rowLeft && colLeft && rowRight && colRight)
        ss << " (" << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight << ")";

    ss << " is not well-sorted";
    return ss.str();
}

string ErrorMessages::buildStackUnpoppable(unsigned long levels) {
    stringstream ss;
    ss << "Stack not deep enough to pop " << levels;
    if (levels == 1)
        ss << " level";
    else
        ss << " levels";

    return ss.str();
}


string ErrorMessages::buildLogicAlreadySet(string logic) {
    return "Logic already set to '" + logic + "'";
}

string ErrorMessages::buildTheoryAlreadyLoaded(string theory) {
    return "Theory '" + theory + "' already loaded";
}

string ErrorMessages::buildConstMultipleSorts(string name, vector<string> &possibleSorts) {
    stringstream ss;
    ss << "Multiple possible sorts for constant '" << name << "': ";
    printArray(ss, possibleSorts, ", ");

    return ss.str();
}

string ErrorMessages::buildConstWrongSort(string name,
                                          string wrongSort,
                                          vector<string> &possibleSorts) {
    stringstream ss;
    ss << "Constant '" << name << "' cannot be of sort " << wrongSort << ". Possible sorts: ";
    printArray(ss, possibleSorts, ", ");

    return ss.str();
}

string ErrorMessages::buildLiteralUnknownSort(string literalType) {
    return "No declared sort for " + literalType + " literals";
}

string ErrorMessages::buildLiteralMultipleSorts(string literalType,
                                                vector<string> &possibleSorts) {
    stringstream ss;
    ss << "Multiple declared sorts for " + literalType + " literals: ";
    printArray(ss, possibleSorts, ", ");
    return ss.str();
}

string ErrorMessages::buildFunUnknownDecl(string name,
                                          string retSort) {
    stringstream ss;
    ss << "No known declaration for function '" << name << "' with return sort " << retSort;
    return ss.str();
}

string ErrorMessages::buildFunUnknownDecl(string name,
                                          unsigned long paramCount,
                                          string retSort) {
    stringstream ss;
    ss << "No known declaration for function '" << name << "' with "
    << paramCount << " parameters and return sort " << retSort;

    return ss.str();
}

string ErrorMessages::buildFunUnknownDecl(string name,
                                          vector<string> argSorts) {
    stringstream ss;
    ss << "No known declaration for function '" << name << "' with parameter list (";
    printArray(ss, argSorts, ", ");
    ss << ")";

    return ss.str();
}

string ErrorMessages::buildFunUnknownDecl(string name,
                                          vector<string> argSorts,
                                          string retSort) {
    stringstream ss;
    ss << buildFunUnknownDecl(name, argSorts) << " and return sort " << retSort;

    return ss.str();
}

string ErrorMessages::buildFunMultipleDecls(string name,
                                            unsigned long paramCount,
                                            string retSort) {
    stringstream ss;
    ss << "Multiple declarations for function '" << name << "' with "
    << paramCount << " parameters and return sort " << retSort;

    return ss.str();
}

string ErrorMessages::buildFunMultipleDecls(string name,
                                            vector<string> argSorts,
                                            vector<string> retSorts) {
    stringstream ss;
    ss << "Multiple declarations for function '" << name << "' with parameter list ";
    printArray(ss, argSorts, ", ");
    ss << ". Possible return sorts: ";
    printArray(ss, retSorts, ", ");

    return ss.str();
}

string ErrorMessages::buildQuantTermWrongSort(string term, string wrongSort, string rightSort,
                                              int rowLeft, int colLeft, int rowRight, int colRight) {
    stringstream ss;
    ss << "Quantified term '" << extractFirstN(term, 50) << "' ("
    << rowLeft << ":" << colLeft << " - " << rowRight << ":" << colRight
    << ") is of type " << wrongSort << ", not " << rightSort;

    return ss.str();
}

string ErrorMessages::buildPatternMismatch(string sort, string pattern) {
    stringstream ss;
    ss << "Cannot match term of sort " << sort << " with pattern " << pattern;

    return ss.str();
}

string ErrorMessages::buildCasesMismatch(vector<string> caseSorts) {
    stringstream ss;
    ss << "Cases have different sorts: ";
    printArray(ss, caseSorts, " ");

    return ss.str();
}