/**
 * \file smt_abstract.h
 * \brief Abstract SMT-LIB data structures.
 */

#ifndef PARSE_SMTLIB_SMT_ABSTRACT_H
#define PARSE_SMTLIB_SMT_ABSTRACT_H

#include <string>

namespace smt {
    namespace ast {
        /**
         * Node of the SMT-LIB abstract syntax tree
         */
        class SmtAstNode {
        public:
            virtual std::string toString() = 0;
        };

        /**
         * Root of the SMT-LIB abstract syntax tree
         */
        class SmtObject : public SmtAstNode {
        };
    }
}

#endif //PARSE_SMTLIB_SMT_ABSTRACT_H