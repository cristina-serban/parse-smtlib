/**
 * \file smt_interfaces.h
 * \brief Interfaces that need to be implemented by some of the SMT-LIB AST nodes
 */
#include "smt_abstract.h"

#ifndef PARSE_SMTLIB_SMT_INTERFACES_H
#define PARSE_SMTLIB_SMT_INTERFACES_H

namespace smt {

    class ICommandOption :  public virtual SmtAstNode { };
    class IAttributeValue : public virtual SmtAstNode { };
    class ISExpression :    public virtual SmtAstNode { };
    class IQualIdentifier : public virtual SmtAstNode { };
    class IIdentifier :     public virtual SmtAstNode,
                            public virtual IQualIdentifier { };
    class IIndex :          public virtual SmtAstNode { };
    class ISpecConstant :   public virtual SmtAstNode { };

}

#endif //PARSE_SMTLIB_SMT_INTERFACES_H
