//
// Created by cristinaserban on 16.04.2015.
//

#ifndef PARSE_SMTLIB_SMT_LOGIC_H
#define PARSE_SMTLIB_SMT_LOGIC_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_attribute.h"

namespace smt {
    class SmtLogic : public SmtObject {
    private:
        std::vector<std::shared_ptr<Attribute>> attributes;

    public:
        SmtLogic() { }
        SmtLogic(std::vector<std::shared_ptr<Attribute>> &attributes);

        std::vector<std::shared_ptr<Attribute>> &getAttributes();
    };
}

#endif //PARSE_SMTLIB_SMT_LOGIC_H
