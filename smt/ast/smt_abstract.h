/**
 * \file smt_abstract.h
 * \brief Abstract SMT-LIB data structures.
 */

#ifndef PARSE_SMTLIB_SMT_ABSTRACT_H
#define PARSE_SMTLIB_SMT_ABSTRACT_H

#include <string>

namespace smt {
    namespace ast {
        /**
         * Node of the SMT-LIB abstract syntax tree
         */
        class SmtAstNode {
        private:
            unsigned int rowL;
            unsigned int colL;
            unsigned int rowR;
            unsigned int colR;
        public:
            virtual std::string toString() = 0;

            inline unsigned int getRowL() {
                return rowL;
            }

            inline unsigned int getColL() {
                return colL;
            }

            inline unsigned int getRowR() {
                return rowR;
            }

            inline unsigned int getColR() {
                return colR;
            }

            inline void setRowL(unsigned int v) {
                rowL = v;
            }

            inline void setColL(unsigned int v) {
                colL = v;
            }

            inline void setRowR(unsigned int v) {
                rowR = v;
            }

            inline void setColR(unsigned int v) {
                colR = v;
            }
        };

        /**
         * Root of the SMT-LIB abstract syntax tree
         */
        class SmtAstRoot : public SmtAstNode {
        };
    }
}

#endif //PARSE_SMTLIB_SMT_ABSTRACT_H