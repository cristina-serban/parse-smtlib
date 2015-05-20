#include <algorithm>
#include <bitset>
#include <iostream>
#include <cmath>
#include <sstream>
#include "smt_literal.h"

using namespace smtlib::ast;
using namespace std;

/* ================================== NumeralLiteral ================================== */

NumeralLiteral::NumeralLiteral(long value, unsigned int base) : base(base) {
    setValue(value);
}

unsigned int NumeralLiteral::getBase() {
    return base;
}

void NumeralLiteral::setBase(unsigned int base) {
    this->base = base;
}

string NumeralLiteral::toString() {
    stringstream ss;

    if (base == 2) {
        ss << "#b";
        if(value == 0)
            ss << 0;
        else {
            stringstream binary;
            while(value != 0) {
                binary <<( value & 1);
                value >>= 1;
            }
            string result = binary.str();
            reverse(result.begin(), result.end());
            ss << result;
        }
    } else if (base == 16) {
        ss << "#x" << std::hex << value;
    } else {
        ss << value;
    }

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
    stringstream ss;
    ss << "\"" << value << "\"";
    return ss.str();
}