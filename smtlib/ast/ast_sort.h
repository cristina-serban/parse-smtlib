/**
 * \file smt_sort.h
 * \brief SMT-LIB sort.
 */

#ifndef PARSE_SMTLIB_AST_SORT_H
#define PARSE_SMTLIB_AST_SORT_H

#include <memory>
#include <vector>
#include "ast_basic.h"
#include "ast_identifier.h"

namespace smtlib {
    namespace ast {
        class Identifier;
        /**
         * An SMT-LIB sort.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class Sort : public AstNode {
        protected:
            std::shared_ptr<Identifier> identifier;
            std::vector<std::shared_ptr<Sort>> params;
        public:

            /**
             * Constructor for a simple sort
             * \param identifier    Sort name
             */
            Sort(std::shared_ptr<Identifier> identifier) : identifier(identifier) { }

            /**
             * Constructor for a parametric sort
             * \param identifier    Sort name
             * \param params        Sort parameters
             */
            Sort(std::shared_ptr<Identifier> identifier,
                 const std::vector<std::shared_ptr<Sort>> &params);

            const std::shared_ptr<Identifier> getIdentifier() const;
            std::shared_ptr<Identifier> getIdentifier();

            void setIdentifier(std::shared_ptr<Identifier> identifier);

            const std::vector<std::shared_ptr<Sort>> &getParams() const;
            std::vector<std::shared_ptr<Sort>> &getParams();

            /**
             * Checks whether the sort is parametrized (i.e. the list of sort parameters is not empty).
             */
            bool isParametrized() const;

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };
    }
}

#endif //PARSE_SMTLIB_AST_SORT_H