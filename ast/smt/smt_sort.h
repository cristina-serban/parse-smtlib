/**
 * \file smt_sort.h
 * \brief Defiition of a sort.
 */

#ifndef PARSE_SMTLIB_SMT_SORT_H
#define PARSE_SMTLIB_SMT_SORT_H

#include <memory>
#include <vector>
#include "smt_basic.h"

namespace smt {
    /**
     * An SMT-LIB sort.
     * Node of the SMT abstract syntax tree.
     */
    class Sort : public SmtAstNode {
    protected:
        std::shared_ptr<IIdentifier> identifier;
        std::vector<std::shared_ptr<Sort>> params;
    public:

        /**
         * Constructor for a simple sort
         * \param identifier    Sort name
         */
        Sort(std::shared_ptr<IIdentifier> identifier);

        /**
         * Constructor for a parametric sort
         * \param identifier    Sort name
         * \param params        Sort parameters
         */
        Sort(std::shared_ptr<IIdentifier> identifier, std::vector<std::shared_ptr<Sort>> &params);

        std::shared_ptr<IIdentifier> getIdentifier();
        void setIdentifier(std::shared_ptr<IIdentifier> identifier);

        std::vector<std::shared_ptr<Sort>> &getParams();

        /**
         * Checks whether the sort is parametric (i.e. the list of parameters is not empty).
         */
        bool isParametric();
    };
}


#endif //PARSE_SMTLIB_SMT_SORT_H
