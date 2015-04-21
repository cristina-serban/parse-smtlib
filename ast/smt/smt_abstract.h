/**
 * \file smt_abstract.h
 * \brief Abstract SMT-LIB data structures.
 */

#ifndef PARSE_SMTLIB_SMT_ABSTRACT_H
#define PARSE_SMTLIB_SMT_ABSTRACT_H

#include "../ast_node.h"

namespace smt {
    class SmtAstNode : public AstNode {
    };

    class SmtObject : public SmtAstNode {
    };
}

#endif //PARSE_SMTLIB_SMT_ABSTRACT_H