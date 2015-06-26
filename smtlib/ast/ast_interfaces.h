/**
 * \file smt_interfaces.h
 * \brief Interfaces that need to be implemented by some of the SMT-LIB AST nodes
 */

#ifndef PARSE_SMTLIB_AST_INTERFACES_H
#define PARSE_SMTLIB_AST_INTERFACES_H

#include "ast_abstract.h"

namespace smtlib {
    namespace ast {

        class AttributeValue : public virtual AstNode {
        };

        class SExpression : public virtual AstNode {
        };

        class Term : public virtual AstNode {
        };

        class QIdentifier : public virtual AstNode,
                            public Term {
        };

        class Index : public virtual AstNode {
        };

        class SpecConstant : public virtual AstNode,
                              public SExpression,
                              public Term,
                              public AttributeValue {
        };
    }
}

#endif //PARSE_SMTLIB_AST_INTERFACES_H