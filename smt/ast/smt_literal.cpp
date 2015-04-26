#include <sstream>
#include "smt_literal.h"

using namespace smt::ast;
using namespace std;

/* ====================================== Literal ===================================== */

template <class T>
T &Literal<T>::getValue() {
    return value;
}

template <class T>
void Literal<T>::setValue(T &value) {
    this->value = value;
}

/* ================================== NumeralLiteral ================================== */

NumeralLiteral::NumeralLiteral(long value) {
    setValue(value);
}

string NumeralLiteral::toString() {
    stringstream ss;
    ss << value;
    return ss.str();
}

/* ================================== DecimalLiteral ================================== */

DecimalLiteral::DecimalLiteral(double value) {
    setValue(value);
}

string DecimalLiteral::toString() {
    stringstream ss;
    ss << value;
    return ss.str();
}

/* ================================== StringLiteral =================================== */

StringLiteral::StringLiteral(string value) {
    setValue(value);
}

string StringLiteral::toString() {
    return value;
}