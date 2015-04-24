/**
 * \file smt_identif.h
 * \brief SMT-LIB identifiers.
 */

#ifndef PARSE_SMTLIB_SMT_IDENTIFIER_H
#define PARSE_SMTLIB_SMT_IDENTIFIER_H

#include <memory>
#include <vector>
#include "smt_basic.h"
#include "smt_interfaces.h"

namespace smt {
    namespace ast {
        class Sort;  // To avoid circular inclusion of header files

        /* ==================================== Identifier ==================================== */
        /**
         * Identifier (e.g. "Real", "|John Brown|", "_ BitVec 32").
         */
        class Identifier : public IQualIdentifier {
        private:
            std::shared_ptr<Symbol> symbol;
            std::vector<std::shared_ptr<IIndex>> indices;

        public:
            /**
             * Constuctor for unindexed identifier.
             * \param symbol    Identifier symbol
             */
            Identifier(std::shared_ptr<Symbol> symbol) : symbol(symbol) { }

            /**
             * Constuctor for indexed identifier.
             * \param symbol    Identifier symbol
             * \param indices   Identifier indices
             */
            Identifier(std::shared_ptr<Symbol> symbol,
                       const std::vector<std::shared_ptr<IIndex>> indices);

            std::shared_ptr<Symbol> getSymbol();
            void setSymbol(std::shared_ptr<Symbol> symbol);

            std::vector<std::shared_ptr<IIndex>> &getIndices();

            /**
             * Checks whether the identifier is indexed (i.e. the list of indices is not empty).
             */
            bool isIndexed();
        };

        /* =============================== QualifiedIdentifier ================================ */
        /**
         * Qualified identifier (e.g. "(as f Sigma)").
         */
        class QualifiedIdentifier : public IQualIdentifier {
        private:
            std::shared_ptr<Identifier> identifier;
            std::shared_ptr<Sort> sort;
        public:
            /**
             * \param identifier    Identifier
             * \param sort          Result sort
             */
            QualifiedIdentifier(std::shared_ptr<Identifier> identifier,
                                std::shared_ptr<Sort> sort) :
                    identifier(identifier), sort(sort) { }

            std::shared_ptr<Identifier> getIdentifier();
            void setIdentifier(std::shared_ptr<Identifier> identifier);

            std::shared_ptr<Sort> getSort();
            void setSort(std::shared_ptr<Sort> sort);
        };
    }
}

#endif //PARSE_SMTLIB_SMT_IDENTIFIER_H