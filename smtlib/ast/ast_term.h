/**
 * \file smt_term.h
 * \brief SMT-LIB terms.
 */

#ifndef PARSE_SMTLIB_AST_TERM_H
#define PARSE_SMTLIB_AST_TERM_H

#include <memory>
#include <vector>
#include "ast_interfaces.h"
#include "ast_var.h"
#include "ast_attribute.h"

namespace smtlib {
    namespace ast {
        /* ================================== QualifiedTerm =================================== */
        /**
         * A list of terms preceded by a qualified identifier.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class QualifiedTerm : public Term {
        private:
            std::shared_ptr<QIdentifier> identifier;
            std::vector<std::shared_ptr<Term>> terms;

        public:
            /**
             * \param identifier    Qualified identifier
             * \param terms         List of terms
             */
            QualifiedTerm(std::shared_ptr<QIdentifier> identifier,
                          const std::vector<std::shared_ptr<Term>> &terms);

            std::shared_ptr<QIdentifier> getIdentifier() const;
            void setIdentifier(std::shared_ptr<QIdentifier> identifier);

            std::vector<std::shared_ptr<Term>> &getTerms();
            std::vector<std::shared_ptr<Term>> getTerms() const;

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };

        /* ===================================== LetTerm ====================================== */
        /**
         * Term preceded by a let binder.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class LetTerm : public Term {
        private:
            std::vector<std::shared_ptr<VarBinding>> bindings;
            std::shared_ptr<Term> term;

        public:
            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            LetTerm(const std::vector<std::shared_ptr<VarBinding>> &bindings,
                    std::shared_ptr<Term> term);

            std::shared_ptr<Term> getTerm() const;
            void setTerm(std::shared_ptr<Term> term);

            std::vector<std::shared_ptr<VarBinding>> &getBindings();
            std::vector<std::shared_ptr<VarBinding>> getBindings() const;

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };

        /* ==================================== ForallTerm ==================================== */
        /**
         * Term preceded by a forall binder.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ForallTerm : public Term {
        private:
            std::vector<std::shared_ptr<SortedVariable>> bindings;
            std::shared_ptr<Term> term;

        public:
            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            ForallTerm(const std::vector<std::shared_ptr<SortedVariable>> &bindings,
                       std::shared_ptr<Term> term);

            std::shared_ptr<Term> getTerm() const;
            void setTerm(std::shared_ptr<Term> term);

            std::vector<std::shared_ptr<SortedVariable>> &getBindings();
            std::vector<std::shared_ptr<SortedVariable>> getBindings() const;

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };

        /* ==================================== ExistsTerm ==================================== */
        /**
         * Term preceded by an exists binder.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ExistsTerm : public Term {
        private:
            std::vector<std::shared_ptr<SortedVariable>> bindings;
            std::shared_ptr<Term> term;

        public:
            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            ExistsTerm(const std::vector<std::shared_ptr<SortedVariable>> &bindings,
                       std::shared_ptr<Term> term);

            std::shared_ptr<Term> getTerm() const;
            void setTerm(std::shared_ptr<Term> term);

            std::vector<std::shared_ptr<SortedVariable>> &getBindings();
            std::vector<std::shared_ptr<SortedVariable>> getBindings() const;

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };

        /* ================================== AnnotatedTerm =================================== */
        /**
         * An annotated term.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class AnnotatedTerm : public Term {
        private:
            std::shared_ptr<Term> term;
            std::vector<std::shared_ptr<Attribute>> attrs;

        public:
            /**
             * \param term  Inner term
             * \param attr  Attributes
             */
            AnnotatedTerm(std::shared_ptr<Term> term,
                          const std::vector<std::shared_ptr<Attribute>> &attrs);

            std::shared_ptr<Term> getTerm() const;
            void setTerm(std::shared_ptr<Term> term);

            std::vector<std::shared_ptr<Attribute>> &getAttrs();
            std::vector<std::shared_ptr<Attribute>> getAttrs() const;

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_TERM_H