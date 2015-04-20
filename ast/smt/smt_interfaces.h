//
// Created by cristinaserban on 16.04.2015.
//

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
