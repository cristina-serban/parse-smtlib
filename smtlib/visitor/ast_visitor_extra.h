#ifndef PARSE_SMTLIB_AST_VISITOR_EXTRA_H
#define PARSE_SMTLIB_AST_VISITOR_EXTRA_H

#include "ast_visitor.h"
#include "../ast/ast_abstract.h"
#include "../util/logger.h"

namespace smtlib {
    namespace ast {
        template<class RetT>
        class AstVisitor1 : public virtual AstVisitor0 {
        protected:
            RetT ret;
            RetT wrappedVisit(std::shared_ptr<AstNode> node) {
                RetT oldRet = ret;
                visit0(node);
                RetT newRet = ret;
                ret = oldRet;
                return newRet;
            }
        public:
            virtual RetT run (std::shared_ptr<AstNode> node) {
                return wrappedVisit(node);
            }
        };

        template<class RetT, class ArgT>
        class AstVisitor2 : public virtual AstVisitor0 {
        protected:
            ArgT arg;
            RetT ret;

            RetT wrappedVisit(ArgT arg, std::shared_ptr<AstNode> node) {
                RetT oldRet = ret;
                ArgT oldArg = this->arg;
                this->arg = arg;
                visit0(node);
                RetT newRet = ret;
                ret = oldRet;
                this->arg = oldArg;
                return newRet;
            }
        public:
            virtual RetT run(ArgT arg, std::shared_ptr<AstNode> node) {
                return wrappedVisit(arg, node);
            }
        };

        template<class RetT>
        class DummyAstVisitor1 : public AstVisitor1<RetT>,
                                 public DummyAstVisitor0 { };

        template<class RetT, class ArgT>
        class DummyAstVisitor2 : public AstVisitor2<RetT, ArgT>,
                                 public DummyAstVisitor0 { };
    }
}

#endif //PARSE_SMTLIB_AST_VISITOR_EXTRA_H