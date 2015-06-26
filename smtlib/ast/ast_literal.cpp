#include "ast_literal.h"

#include <algorithm>
#include <bitset>
#include <cmath>
#include <iostream>
#include <sstream>

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

void NumeralLiteral::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string NumeralLiteral::toString() {
    stringstream ss;

    if (base == 2) {
        ss << "#b";
        if(value == 0)
            ss << 0;
        else {
            long val = value;
            stringstream binary;
            while(val != 0) {
                binary << (val & 1);
                val >>= 1;
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

void DecimalLiteral::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
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

void StringLiteral::accept(AstVisitor0* visitor){
    visitor->visit(shared_from_this());
}

string StringLiteral::toString() {
    stringstream ss;
    ss << value;
    return ss.str();
}