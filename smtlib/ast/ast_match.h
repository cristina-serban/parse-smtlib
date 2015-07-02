#ifndef PARSE_SMTLIB_AST_MATCH_H
#define PARSE_SMTLIB_AST_MATCH_H

#include "ast_abstract.h"
#include "ast_basic.h"
#include "ast_interfaces.h"

#include <vector>

namespace smtlib {
    namespace ast {
        /* =============================== QualifiedConstructor =============================== */
        class QualifiedConstructor : public Constructor,
                                     public std::enable_shared_from_this<QualifiedConstructor> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<Sort> sort;
        public:
            QualifiedConstructor(std::shared_ptr<Symbol> symbol, std::shared_ptr<Sort> sort);

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::shared_ptr<Sort> getSort() { return sort; }

            inline void setSort(std::shared_ptr<Sort> sort) { this->sort = sort; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= QualifiedPattern ================================= */
        class QualifiedPattern : public Pattern,
                                 public std::enable_shared_from_this<QualifiedPattern> {
        private:
            std::shared_ptr<Constructor> constructor;
            std::vector<std::shared_ptr<Symbol>> symbols;
        public:
            QualifiedPattern(std::shared_ptr<Constructor> constructor,
                             std::vector<std::shared_ptr<Symbol>>& symbols);

            inline std::shared_ptr<Constructor> getConstructor() { return constructor; }

            inline void setConstructor(std::shared_ptr<Constructor> constructor) { this->constructor = constructor; }

            inline std::vector<std::shared_ptr<Symbol>>& getSymbols() { return symbols; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ===================================== MatchCase ==================================== */
        class MatchCase : public AstNode,
                          public std::enable_shared_from_this<MatchCase> {
        private:
            std::shared_ptr<Pattern> pattern;
            std::shared_ptr<Term> term;
        public:
            MatchCase(std::shared_ptr<Pattern> pattern,
                      std::shared_ptr<Term> term);

            inline std::shared_ptr<Pattern> getPattern() { return pattern;}

            inline void setPattern(std::shared_ptr<Pattern> pattern) { this->pattern = pattern;}

            inline std::shared_ptr<Term> getTerm() { return term; }

            inline void setTerm(std::shared_ptr<Term> term) { this->term = term; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_MATCH_H
