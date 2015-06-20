/**
 * \file ast_abstract.h
 * \brief Abstract SMT-LIB data structures.
 */

#ifndef PARSE_SMTLIB_AST_ABSTRACT_H
#define PARSE_SMTLIB_AST_ABSTRACT_H

#include <memory>
#include <string>
#include "../visitor/ast_visitor.h"

namespace smtlib {
    namespace ast {

        /**
         * Node of the SMT-LIB abstract syntax tree
         */
        class AstNode {
        private:
            int rowLeft;
            int rowRight;
            int colLeft;
            int colRight;
        public:
            virtual std::string toString() const = 0;

            virtual void accept(AstVisitor0 *visitor) const = 0;

            int getRowLeft() const {
                return rowLeft;
            }

            void setRowLeft(int rowLeft) {
                this->rowLeft = rowLeft;
            }

            int getRowRight() const {
                return rowRight;
            }

            void setRowRight(int rowRight) {
                this->rowRight = rowRight;
            }

            int getColLeft() const {
                return colLeft;
            }

            void setColLeft(int colLeft) {
                this->colLeft = colLeft;
            }

            int getColRight() const {
                return colRight;
            }

            void setColRight(int colRight) {
                this->colRight = colRight;
            }
        };

        /**
         * Root of the SMT-LIB abstract syntax tree
         */
        class AstRoot : public AstNode {
        };
    }
}

#endif //PARSE_SMTLIB_AST_ABSTRACT_H