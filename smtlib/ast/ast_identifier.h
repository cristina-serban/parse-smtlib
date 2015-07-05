/**
 * \file smt_identif.h
 * \brief SMT-LIB identifiers.
 */

#ifndef PARSE_SMTLIB_AST_IDENTIFIER_H
#define PARSE_SMTLIB_AST_IDENTIFIER_H

#include "ast_basic.h"
#include "ast_interfaces.h"
#include "ast_sort.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        class Sort;

        /* ==================================== SimpleIdentifier ==================================== */
        /**
         * Simple identifier (e.g. "Real", "|John Brown|", "_ BitVec 32").
         */
        class SimpleIdentifier : public Identifier,
                                 public std::enable_shared_from_this<SimpleIdentifier> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::vector<std::shared_ptr<Index>> indices;

        public:
            /**
             * Constuctor for unindexed identifier.
             * \param symbol    Identifier symbol
             */
            SimpleIdentifier(std::shared_ptr<Symbol> symbol) : symbol(symbol) { }

            /**
             * Constuctor for indexed identifier.
             * \param symbol    Identifier symbol
             * \param indices   Identifier indices
             */
            SimpleIdentifier(std::shared_ptr<Symbol> symbol,
                             std::vector<std::shared_ptr<Index>>& indices);

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::vector<std::shared_ptr<Index>>& getIndices() { return indices; }

            /**
             * Checks whether the identifier is indexed (i.e. the list of indices is not empty).
             */
            bool isIndexed();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== QualifiedIdentifier ================================ */
        /**
         * Qualified identifier (e.g. "(as f Sigma)").
         */
        class QualifiedIdentifier : public Identifier, public std::enable_shared_from_this<QualifiedIdentifier> {
        private:
            std::shared_ptr<SimpleIdentifier> identifier;
            std::shared_ptr<Sort> sort;
        public:
            /**
             * \param identifier    SimpleIdentifier
             * \param sort          Result sort
             */
            inline QualifiedIdentifier(std::shared_ptr<SimpleIdentifier> identifier,
                                       std::shared_ptr<Sort> sort) :
                    identifier(identifier), sort(sort) { }

            inline std::shared_ptr<SimpleIdentifier> getIdentifier() { return identifier; }

            inline void setIdentifier(std::shared_ptr<SimpleIdentifier> identifier) { this->identifier = identifier; }

            inline std::shared_ptr<Sort> getSort() { return sort; }

            inline void setSort(std::shared_ptr<Sort> sort) { this->sort = sort; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_IDENTIFIER_H