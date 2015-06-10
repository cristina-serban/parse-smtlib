#include <visitor/ast_visitor.h>
#include <ast/smt_abstract.h>

using namespace smtlib::ast;

template<class RetT>
RetT AstVisitor1<RetT>::wrappedVisit(AstNode const *node) {
    node->accept(this);
    return this->ret;
}

template<class RetT>
RetT AstVisitor1<RetT>::run(AstNode const *node) {
    return wrappedVisit(node);
}

template<class RetT, class ArgT>
RetT AstVisitor2<RetT, ArgT>::wrappedVisit(ArgT arg, AstNode const *node) {
    this->arg = arg;
    node->accept(this);
    return this->ret;
}

template<class RetT, class ArgT>
RetT AstVisitor2<RetT, ArgT>::run(ArgT arg, AstNode const *node) {
    return wrappedVisit(arg, node);
}