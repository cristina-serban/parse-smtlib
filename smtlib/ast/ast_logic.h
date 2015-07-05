/**
 * \file smt_logic
 * \brief SMT-LIB logic.
 */

#ifndef PARSE_SMTLIB_AST_LOGIC_H
#define PARSE_SMTLIB_AST_LOGIC_H

#include "ast_abstract.h"
#include "ast_attribute.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /**
         * SMT-LIB logic.
         * Node and (possible) root of the SMT abstract syntax tree.
         * Represents the contents of a logic file.
         */
        class Logic : public AstRoot, public std::enable_shared_from_this<Logic> {
        private:
            std::shared_ptr<Symbol> name;
            std::vector<std::shared_ptr<Attribute>> attributes;

        public:
            /**
             * Constructs logic without attributes.
             * \param name          Logic name
             */
            inline Logic(std::shared_ptr<Symbol> name) : name(name) { }

            /**
             * Constructs logic with attributes.
             * \param name          Logic name
             * \param attributes    Logic attributes
             */
            Logic(std::shared_ptr<Symbol> name,
                     std::vector<std::shared_ptr<Attribute>>& attributes);

            inline std::shared_ptr<Symbol> getName() { return name; }

            inline void setName(std::shared_ptr<Symbol> name) { this->name = name; }

            inline std::vector<std::shared_ptr<Attribute>>& getAttributes() { return attributes; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_LOGIC_H