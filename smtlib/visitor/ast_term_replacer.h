#ifndef PARSE_SMTLIB_AST_MUPREC_GENERATOR_H
#define PARSE_SMTLIB_AST_MUPREC_GENERATOR_H

#include <fstream>
#include "../ast/ast_interfaces.h"
#include "ast_visitor_extra.h"

namespace smtlib {
    namespace ast {
        /* =============================== ITermReplacerContext =============================== */
        class ITermReplacerContext {
        public:
            virtual std::shared_ptr<Term> getTerm() = 0;
            virtual void setTerm(std::shared_ptr<Term> term) = 0;

            virtual std::shared_ptr<Term> getExpression() = 0;
            virtual void setExpression(std::shared_ptr<Term> expr) = 0;
        };

        /* =============================== TermReplacerContext ================================ */
        class TermReplacerContext: public ITermReplacerContext {
        private:
            std::shared_ptr<Term> term;
            std::shared_ptr<Term> expr;

        public:
            TermReplacerContext(std::shared_ptr<Term> term, std::shared_ptr<Term> expr)
                    : term(term), expr(expr) {}

            virtual std::shared_ptr<Term> getTerm() { return term; }
            virtual void setTerm(std::shared_ptr<Term> term) { this->term = term; }

            virtual std::shared_ptr<Term> getExpression() { return expr; }
            virtual void setExpression(std::shared_ptr<Term> expr) { this->expr = expr; }
        };

        /* =================================== TermReplacer =================================== */
        class TermReplacer : public DummyAstVisitor0,
                             public std::enable_shared_from_this<TermReplacer> {
        private:
            std::shared_ptr<ITermReplacerContext> ctx;
        public:
            inline TermReplacer(std::shared_ptr<ITermReplacerContext> ctx) : ctx(ctx) { }

            virtual void visit(std::shared_ptr<QualifiedTerm> node);
            virtual void visit(std::shared_ptr<LetTerm> node);
            virtual void visit(std::shared_ptr<ForallTerm> node);
            virtual void visit(std::shared_ptr<ExistsTerm> node);
            virtual void visit(std::shared_ptr<MatchTerm> node);
            virtual void visit(std::shared_ptr<AnnotatedTerm> node);
        };
    }
}

#endif //PARSE_SMTLIB_AST_MUPREC_GENERATOR_H
