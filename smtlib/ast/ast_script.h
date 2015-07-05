/**
 * \file smt_script
 * \brief SMT-LIB script.
 */

#ifndef PARSE_SMTLIB_AST_SCRIPT_H
#define PARSE_SMTLIB_AST_SCRIPT_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_command.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /**
         * SMT-LIB script.
         * Node and (possible) root of the SMT abstract syntax tree.
         * Represents the contents of a query file.
         */
        class Script : public AstRoot, public std::enable_shared_from_this<Script> {
        private:
            std::vector<std::shared_ptr<Command>> commands;

        public:
            /**
             * Default constructor
             */
            inline Script() { }

            /**
             * \param cmds    Command list
             */
            Script(std::vector<std::shared_ptr<Command>>& commands);

            inline std::vector<std::shared_ptr<Command>>& getCommands() { return commands; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_SCRIPT_H