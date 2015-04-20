//
// Created by cristinaserban on 17.04.2015.
//

#ifndef PARSE_SMTLIB_SMT_SORT_H
#define PARSE_SMTLIB_SMT_SORT_H

#include <memory>
#include <vector>
#include "smt_basic.h"

namespace smt {
    class Sort : public SmtAstNode {
    protected:
        std::shared_ptr<IIdentifier> identifier;
        std::vector<std::shared_ptr<Sort>> params;
    public:
        Sort(std::shared_ptr<IIdentifier> identifier);
        Sort(std::shared_ptr<IIdentifier> identifier, std::vector<std::shared_ptr<Sort>> &params);

        std::shared_ptr<IIdentifier> getIdentifier();
        void setIdentifier(std::shared_ptr<IIdentifier> identifier);

        std::vector<std::shared_ptr<Sort>> &getParams();
    };
}


#endif //PARSE_SMTLIB_SMT_SORT_H
