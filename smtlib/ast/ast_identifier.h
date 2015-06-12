/**
 * \file smt_identif.h
 * \brief SMT-LIB identifiers.
 */

#ifndef PARSE_SMTLIB_AST_IDENTIFIER_H
#define PARSE_SMTLIB_AST_IDENTIFIER_H

#include <memory>
#include <vector>
#include "ast_basic.h"
#include "ast_interfaces.h"
#include "ast_sort.h"

namespace smtlib {
    namespace ast {
       class Sort;

        /* ==================================== Identifier ==================================== */
        /**
         * Identifier (e.g. "Real", "|John Brown|", "_ BitVec 32").
         */
        class Identifier : public QIdentifier {
        private:
            std::shared_ptr<Symbol> symbol;
            std::vector<std::shared_ptr<Index>> indices;

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
                       const std::vector<std::shared_ptr<Index>> indices);

            std::shared_ptr<Symbol> getSymbol() const;
            void setSymbol(std::shared_ptr<Symbol> symbol);

            std::vector<std::shared_ptr<Index>> &getIndices();
            std::vector<std::shared_ptr<Index>> getIndices() const;

            /**
             * Checks whether the identifier is indexed (i.e. the list of indices is not empty).
             */
            bool isIndexed() const;

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };

        /* =============================== QualifiedIdentifier ================================ */
        /**
         * Qualified identifier (e.g. "(as f Sigma)").
         */
        class QualifiedIdentifier : public QIdentifier {
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

            std::shared_ptr<Identifier> getIdentifier() const;
            void setIdentifier(std::shared_ptr<Identifier> identifier);

            std::shared_ptr<Sort> getSort() const;
            void setSort(std::shared_ptr<Sort> sort);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_IDENTIFIER_H