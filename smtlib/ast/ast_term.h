/**
 * \file smt_term.h
 * \brief SMT-LIB terms.
 */

#ifndef PARSE_SMTLIB_AST_TERM_H
#define PARSE_SMTLIB_AST_TERM_H

#include "ast_attribute.h"
#include "ast_interfaces.h"
#include "ast_var.h"
#include "ast_match.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /* ================================== QualifiedTerm =================================== */
        /**
         * A list of terms preceded by a qualified identifier.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class QualifiedTerm : public Term, public std::enable_shared_from_this<QualifiedTerm> {
        private:
            std::shared_ptr<Identifier> identifier;
            std::vector<std::shared_ptr<Term>> terms;

        public:
            /**
             * \param identifier    Qualified identifier
             * \param terms         List of terms
             */
            QualifiedTerm(std::shared_ptr<Identifier> identifier,
                          std::vector<std::shared_ptr<Term>> &terms);

            std::shared_ptr<Identifier> getIdentifier();

            void setIdentifier(std::shared_ptr<Identifier> identifier);

            std::vector<std::shared_ptr<Term>> &getTerms();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== LetTerm ====================================== */
        /**
         * Term preceded by a let binder.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class LetTerm : public Term, public std::enable_shared_from_this<LetTerm> {
        private:
            std::vector<std::shared_ptr<VarBinding>> bindings;
            std::shared_ptr<Term> term;

        public:
            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            LetTerm(std::vector<std::shared_ptr<VarBinding>> &bindings,
                    std::shared_ptr<Term> term);

            std::shared_ptr<Term> getTerm();

            void setTerm(std::shared_ptr<Term> term);

            std::vector<std::shared_ptr<VarBinding>> &getBindings();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== ForallTerm ==================================== */
        /**
         * Term preceded by a forall binder.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ForallTerm : public Term, public std::enable_shared_from_this<ForallTerm> {
        private:
            std::vector<std::shared_ptr<SortedVariable>> bindings;
            std::shared_ptr<Term> term;

        public:
            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            ForallTerm(std::vector<std::shared_ptr<SortedVariable>> &bindings,
                       std::shared_ptr<Term> term);

            std::shared_ptr<Term> getTerm();

            void setTerm(std::shared_ptr<Term> term);

            std::vector<std::shared_ptr<SortedVariable>> &getBindings();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== ExistsTerm ==================================== */
        /**
         * Term preceded by an exists binder.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ExistsTerm : public Term, public std::enable_shared_from_this<ExistsTerm> {
        private:
            std::vector<std::shared_ptr<SortedVariable>> bindings;
            std::shared_ptr<Term> term;

        public:
            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            ExistsTerm(std::vector<std::shared_ptr<SortedVariable>> &bindings,
                       std::shared_ptr<Term> term);

            std::shared_ptr<Term> getTerm();

            void setTerm(std::shared_ptr<Term> term);

            std::vector<std::shared_ptr<SortedVariable>> &getBindings();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== MatchTerm ===================================== */
        class MatchTerm : public Term,
                          public std::enable_shared_from_this<MatchTerm> {
        private:
            std::shared_ptr<Term> term;
            std::vector<std::shared_ptr<MatchCase>> cases;
        public:
            MatchTerm(std::shared_ptr<Term> term,
                      std::vector<std::shared_ptr<MatchCase>>& cases);

            inline std::shared_ptr<Term> getTerm() { return term; }

            void setTerm(std::shared_ptr<Term> term) { this->term = term; }

            std::vector<std::shared_ptr<MatchCase>> &getCases() { return cases; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================== AnnotatedTerm =================================== */
        /**
         * An annotated term.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class AnnotatedTerm : public Term, public std::enable_shared_from_this<AnnotatedTerm> {
        private:
            std::shared_ptr<Term> term;
            std::vector<std::shared_ptr<Attribute>> attributes;

        public:
            /**
             * \param term  Inner term
             * \param attr  Attributes
             */
            AnnotatedTerm(std::shared_ptr<Term> term,
                          std::vector<std::shared_ptr<Attribute>> &attributes);

            std::shared_ptr<Term> getTerm();

            void setTerm(std::shared_ptr<Term> term);

            std::vector<std::shared_ptr<Attribute>> &getAttributes();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_TERM_H