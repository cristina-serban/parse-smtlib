#ifndef PARSE_SMTLIB_AST_VISITOR_EXTRA_H
#define PARSE_SMTLIB_AST_VISITOR_EXTRA_H

#include "ast_visitor.h"
#include "../ast/ast_abstract.h"

namespace smtlib {
    namespace ast {
        template<class RetT>
        class AstVisitor1 : public AstVisitor0 {
        protected:
            RetT ret;

            RetT wrappedVisit(AstNode const *node) {
                node->accept(this);
                return this->ret;
            }
        public:
            virtual RetT run (AstNode const *node) {
                return wrappedVisit(node);
            }
        };

        template<class RetT, class ArgT>
        class AstVisitor2 : public AstVisitor0 {
        protected:
            ArgT arg;
            RetT ret;

            RetT wrappedVisit(ArgT arg, AstNode const *node);
        public:
            virtual RetT run(ArgT arg, AstNode const *node);
        };

    }
}

#endif //PARSE_SMTLIB_AST_VISITOR_EXTRA_H
