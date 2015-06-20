/**
 * \file smt_logic
 * \brief SMT-LIB logic.
 */

#ifndef PARSE_SMTLIB_AST_LOGIC_H
#define PARSE_SMTLIB_AST_LOGIC_H

#include <memory>
#include <vector>
#include "ast_abstract.h"
#include "ast_attribute.h"

namespace smtlib {
    namespace ast {
        /**
         * SMT-LIB logic.
         * Node and (possible) root of the SMT abstract syntax tree.
         * Represents the contents of a logic file.
         */
        class Logic : public AstRoot {
        private:
            std::shared_ptr<Symbol> name;
            std::vector<std::shared_ptr<Attribute>> attributes;

        public:
            /**
             * Constructs logic without attributes.
             * \param name          Logic name
             */
            Logic(std::shared_ptr<Symbol> name) : name(name) { }

            /**
             * Constructs logic with attributes.
             * \param name          Logic name
             * \param attributes    Logic attributes
             */
            Logic(std::shared_ptr<Symbol> name,
                     const std::vector<std::shared_ptr<Attribute>> &attributes);

            const std::shared_ptr<Symbol> getName() const;
            std::shared_ptr<Symbol> getName();

            void setName(std::shared_ptr<Symbol> name);

            const std::vector<std::shared_ptr<Attribute>> &getAttributes() const;
            std::vector<std::shared_ptr<Attribute>> &getAttributes();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };
    }
}

#endif //PARSE_SMTLIB_AST_LOGIC_H