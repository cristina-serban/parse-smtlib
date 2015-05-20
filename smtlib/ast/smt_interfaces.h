/**
 * \file smt_interfaces.h
 * \brief Interfaces that need to be implemented by some of the SMT-LIB AST nodes
 */

#ifndef PARSE_SMTLIB_SMT_INTERFACES_H
#define PARSE_SMTLIB_SMT_INTERFACES_H

#include "smt_abstract.h"

namespace smtlib {
    namespace ast {

        class IAttributeValue : public virtual AstNode {
        };

        class ISExpression : public virtual AstNode {
        };

        class ITerm : public virtual AstNode {
        };

        class IQualIdentifier : public virtual AstNode,
                                public ITerm {
        };

        class IIndex : public virtual AstNode {
        };

        class ISpecConstant : public virtual AstNode,
                              public ISExpression,
                              public ITerm,
                              public IAttributeValue{
        };
    }
}

#endif //PARSE_SMTLIB_SMT_INTERFACES_H