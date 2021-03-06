/**
 * \file smt_sort.h
 * \brief SMT-LIB sort.
 */

#ifndef PARSE_SMTLIB_AST_SORT_H
#define PARSE_SMTLIB_AST_SORT_H

#include "ast_basic.h"
#include "ast_identifier.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        class SimpleIdentifier;
        /**
         * An SMT-LIB sort.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class Sort : public AstNode, public std::enable_shared_from_this<Sort> {
        protected:
            std::shared_ptr<SimpleIdentifier> identifier;
            std::vector<std::shared_ptr<Sort>> args;
        public:

            /**
             * Constructor for a simple sort
             * \param identifier    Sort name
             */
            inline Sort(std::shared_ptr<SimpleIdentifier> identifier) : identifier(identifier) { }

            /**
             * Constructor for a parametric sort
             * \param identifier    Sort name
             * \param args          Sort arguments
             */
            Sort(std::shared_ptr<SimpleIdentifier> identifier,
                 std::vector<std::shared_ptr<Sort>>& args);

            inline std::shared_ptr<SimpleIdentifier> getIdentifier() { return identifier; }

            inline void setIdentifier(std::shared_ptr<SimpleIdentifier> identifier) { this->identifier = identifier; }

            inline std::vector<std::shared_ptr<Sort>>& getArgs() { return args; }

            /**
             * Checks whether the sort is parametrized (i.e. the list of sort parameters is not empty).
             */
            bool hasArgs();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_SORT_H