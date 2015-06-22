/**
 * \file smt_theory.h
 * \brief SMT-LIB theory.
 */

#ifndef PARSE_SMTLIB_AST_THEORY_H
#define PARSE_SMTLIB_AST_THEORY_H

#include "ast_abstract.h"
#include "ast_attribute.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {

        /**
         * SMT-LIB theory.
         * Node and (possible) root of the SMT abstract syntax tree.
         * Represents the contents of a theory file.
         */
        class Theory : public AstRoot {
        private:
            std::shared_ptr<Symbol> name;
            std::vector<std::shared_ptr<Attribute>> attributes;

        public:
            /**
             * Constructs theory without attributes.
             * \param name  Theory name
             */
            Theory(std::shared_ptr<Symbol> name) : name(name) { }

            /**
             * Constructs theory with attributes.
             * \param name          Theory name
             * \param attributes    Theory attributes
             */
            Theory(std::shared_ptr<Symbol> name,
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

#endif //PARSE_SMTLIB_AST_THEORY_H