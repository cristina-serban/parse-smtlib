/**
 * \file smt_term.h
 * \brief SMT-LIB terms.
 */

#ifndef PARSE_SMTLIB_SMT_TERM_H
#define PARSE_SMTLIB_SMT_TERM_H

#include <memory>
#include <vector>
#include "smt_interfaces.h"
#include "smt_var.h"
#include "smt_attribute.h"

namespace smt {
    namespace ast {
        /* ================================== QualifiedTerm =================================== */
        /**
         * A list of terms preceded by a qualified identifier.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class QualifiedTerm : public ITerm {
        private:
            std::shared_ptr<IQualIdentifier> identifier;
            std::vector<std::shared_ptr<ITerm>> terms;

        public:
            /**
             * \param identifier    Qualified identifier
             * \param terms         List of terms
             */
            QualifiedTerm(std::shared_ptr<IQualIdentifier> identifier,
                          std::vector<std::shared_ptr<ITerm>> &terms);

            std::shared_ptr<IQualIdentifier> getIdentifier();
            void setIdentifier(std::shared_ptr<IQualIdentifier> identifier);

            std::vector<std::shared_ptr<ITerm>> &getTerms();
        };

        /* ===================================== LetTerm ====================================== */
        /**
         * Term preceded by a let binder.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class LetTerm : public ITerm {
        private:
            std::vector<std::shared_ptr<VarBinding>> bindings;
            std::shared_ptr<ITerm> term;

        public:
            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            LetTerm(std::vector<std::shared_ptr<VarBinding>> &bindings,
                    std::shared_ptr<ITerm> term);

            std::shared_ptr<ITerm> getTerm();
            void setTerm(std::shared_ptr<ITerm> term);

            std::vector<std::shared_ptr<VarBinding>> &getBindings();
        };

        /* ==================================== ForallTerm ==================================== */
        /**
         * Term preceded by a forall binder.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ForallTerm : public ITerm {
        private:
            std::vector<std::shared_ptr<SortedVariable>> bindings;
            std::shared_ptr<ITerm> term;

        public:
            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            ForallTerm(std::vector<std::shared_ptr<SortedVariable>> &bindings,
                       std::shared_ptr<ITerm> term);

            std::shared_ptr<ITerm> getTerm();
            void setTerm(std::shared_ptr<ITerm> term);

            std::vector<std::shared_ptr<SortedVariable>> &getBindings();
        };

        /* ==================================== ExistsTerm ==================================== */
        /**
         * Term preceded by an exists binder.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ExistsTerm : public ITerm {
        private:
            std::vector<std::shared_ptr<SortedVariable>> bindings;
            std::shared_ptr<ITerm> term;

        public:
            /**
             * \param bindings  List of bound variables
             * \param term      Inner term
             */
            ExistsTerm(std::vector<std::shared_ptr<SortedVariable>> &bindings,
                       std::shared_ptr<ITerm> term);

            std::shared_ptr<ITerm> getTerm();
            void setTerm(std::shared_ptr<ITerm> term);

            std::vector<std::shared_ptr<SortedVariable>> &getBindings();
        };

        /* ================================== AnnotatedTerm =================================== */
        /**
         * An annotated term.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class AnnotatedTerm : public ITerm {
        private:
            std::shared_ptr<ITerm> term;
            std::vector<std::shared_ptr<Attribute>> attrs;

        public:
            /**
             * \param term  Inner term
             * \param attr  Attributes
             */
            AnnotatedTerm(std::shared_ptr<ITerm> term,
                          std::vector<std::shared_ptr<Attribute>> &attrs);

            std::shared_ptr<ITerm> getTerm();
            void setTerm(std::shared_ptr<ITerm> term);

            std::vector<std::shared_ptr<Attribute>> &getAttrs();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_TERM_H