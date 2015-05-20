/**
 * \file smt_abstract.h
 * \brief Abstract SMT-LIB data structures.
 */

#ifndef PARSE_SMTLIB_SMT_ABSTRACT_H
#define PARSE_SMTLIB_SMT_ABSTRACT_H

#include <string>

namespace smtlib {
    namespace ast {
        /**
         * Node of the SMT-LIB abstract syntax tree
         */
        class AstNode {
        public:
            virtual std::string toString() = 0;
        };

        /**
         * Root of the SMT-LIB abstract syntax tree
         */
        class AstRoot : public AstNode {
        };
    }
}

#endif //PARSE_SMTLIB_SMT_ABSTRACT_H