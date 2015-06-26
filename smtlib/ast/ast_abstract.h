/**
 * \file ast_abstract.h
 * \brief Abstract SMT-LIB data structures.
 */

#ifndef PARSE_SMTLIB_AST_ABSTRACT_H
#define PARSE_SMTLIB_AST_ABSTRACT_H

#include "../visitor/ast_visitor.h"

#include <string>
#include <memory>

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
            std::shared_ptr<std::string> filename;
        public:
            virtual std::string toString() = 0;

            virtual void accept(AstVisitor0* visitor) = 0;

            int getRowLeft() {
                return rowLeft;
            }

            void setRowLeft(int rowLeft) {
                this->rowLeft = rowLeft;
            }

            int getRowRight() {
                return rowRight;
            }

            void setRowRight(int rowRight) {
                this->rowRight = rowRight;
            }

            int getColLeft() {
                return colLeft;
            }

            void setColLeft(int colLeft) {
                this->colLeft = colLeft;
            }

            int getColRight() {
                return colRight;
            }

            void setColRight(int colRight) {
                this->colRight = colRight;
            }

            std::shared_ptr<std::string> getFilename() {
                return filename;
            }

            void setFilename(std::shared_ptr<std::string> filename) {
                this->filename = filename;
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