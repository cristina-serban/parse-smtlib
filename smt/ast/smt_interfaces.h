/**
 * \file smt_interfaces.h
 * \brief Interfaces that need to be implemented by some of the SMT-LIB AST nodes
 */

#ifndef PARSE_SMTLIB_SMT_INTERFACES_H
#define PARSE_SMTLIB_SMT_INTERFACES_H

#include "smt_abstract.h"

namespace smt {
    namespace ast {

        class IAttributeValue : public virtual SmtAstNode {
        };

        class ISExpression : public virtual SmtAstNode {
        };

        class ITerm : public virtual SmtAstNode {
        };

        class IQualIdentifier : public virtual SmtAstNode,
                                public ITerm {
        };

        class IIndex : public virtual SmtAstNode {
        };

        class ISpecConstant : public virtual SmtAstNode,
                              public ISExpression,
                              public ITerm {
        };
    }
}

#endif //PARSE_SMTLIB_SMT_INTERFACES_H