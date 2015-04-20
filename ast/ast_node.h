//
// Created by cristinaserban on 16.04.2015.
//

#ifndef PARSE_SMTLIB_ASTNODE_H
#define PARSE_SMTLIB_ASTNODE_H

#include <string>

namespace smt {
    class AstNode {
    public:
        virtual std::string toString() = 0;
    };
}


#endif //PARSE_SMTLIB_ASTNODE_H
