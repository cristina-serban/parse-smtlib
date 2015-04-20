//
// Created by cristinaserban on 17.04.2015.
//

#include "smt_literal.h"

using namespace smt;
using namespace std;

template <class T>
T& Literal<T>::getValue() {
    return value;
}

template <class T>
void Literal<T>::setValue(T& value) {
    this->value = value;
}

NumeralLiteral::NumeralLiteral(long value) {
    this->value = value;
}

DecimalLiteral::DecimalLiteral(double value) {
    this->value = value;
}

StringLiteral::StringLiteral(string value) {
    this->value = value;
}