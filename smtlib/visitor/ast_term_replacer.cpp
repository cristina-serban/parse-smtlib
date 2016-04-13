#include "ast_term_replacer.h"
#include "../ast/ast_term.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

void TermReplacer::visit(shared_ptr<QualifiedTerm> node) {
    vector<shared_ptr<Term>> &terms = node->getTerms();
    unsigned long size = terms.size();

    for (int i = 0; i < size; i++) {
        if(terms[i]->toString() == ctx->getTerm()->toString())
            terms[i] = ctx->getExpression();
        else
            visit0(terms[i]);
    }
}

void TermReplacer::visit(shared_ptr<LetTerm> node) {
    if(node->getTerm()->toString() == ctx->getTerm()->toString()) {
        node->setTerm(ctx->getExpression());
    } else {
        visit0(node->getTerm());
    }
}

void TermReplacer::visit(shared_ptr<ForallTerm> node) {
    if(node->getTerm()->toString() == ctx->getTerm()->toString()) {
        node->setTerm(ctx->getExpression());
    } else {
        visit0(node->getTerm());
    }
}

void TermReplacer::visit(shared_ptr<ExistsTerm> node) {
    if(node->getTerm()->toString() == ctx->getTerm()->toString()) {
        node->setTerm(ctx->getExpression());
    } else {
        visit0(node->getTerm());
    }
}

void TermReplacer::visit(shared_ptr<MatchTerm> node) {
    if(node->getTerm()->toString() == ctx->getTerm()->toString()) {
        node->setTerm(ctx->getExpression());
    } else {
        visit0(node->getTerm());
    }
}

void TermReplacer::visit(shared_ptr<AnnotatedTerm> node) {
    if(node->getTerm()->toString() == ctx->getTerm()->toString()) {
        node->setTerm(ctx->getExpression());
    } else {
        visit0(node->getTerm());
    }
}