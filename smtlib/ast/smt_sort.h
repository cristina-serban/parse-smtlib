/**
 * \file smt_sort.h
 * \brief SMT-LIB sort.
 */

#ifndef PARSE_SMTLIB_SMT_SORT_H
#define PARSE_SMTLIB_SMT_SORT_H

#include <memory>
#include <vector>
#include "smt_basic.h"
#include "smt_identifier.h"

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

            std::shared_ptr<Identifier> getIdentifier();
            void setIdentifier(std::shared_ptr<Identifier> identifier);

            std::vector<std::shared_ptr<Sort>> &getParams();

            /**
             * Checks whether the sort is parametric (i.e. the list of parameters is not empty).
             */
            bool isParametric();

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_SORT_H