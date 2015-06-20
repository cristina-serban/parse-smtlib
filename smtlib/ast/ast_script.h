/**
 * \file smt_script
 * \brief SMT-LIB script.
 */

#ifndef PARSE_SMTLIB_AST_SCRIPT_H
#define PARSE_SMTLIB_AST_SCRIPT_H

#include <memory>
#include <vector>
#include "ast_abstract.h"
#include "ast_command.h"
#include "ast_basic.h"

namespace smtlib {
    namespace ast {
        /**
         * SMT-LIB script.
         * Node and (possible) root of the SMT abstract syntax tree.
         * Represents the contents of a query file.
         */
        class Script : public AstRoot {
        private:
            std::vector<std::shared_ptr<Command>> commands;

        public:
            /**
             * Default constructor
             */
            Script() { }

            /**
             * \param cmds    Command list
             */
            Script(const std::vector<std::shared_ptr<Command>> &cmds);

            const std::vector<std::shared_ptr<Command>> &getCommands() const;
            std::vector<std::shared_ptr<Command>> &getCommands();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };
    }
}

#endif //PARSE_SMTLIB_AST_SCRIPT_H