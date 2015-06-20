/**
 * \file smt_command.h
 * \brief SMT-LIB commands that appear in a query file.
 */

#ifndef PARSE_SMTLIB_AST_COMMAND_H
#define PARSE_SMTLIB_AST_COMMAND_H

#include <memory>
#include <vector>
#include "ast_abstract.h"
#include "ast_interfaces.h"
#include "ast_basic.h"
#include "ast_sort.h"
#include "ast_literal.h"
#include "ast_fun.h"
#include "ast_attribute.h"

namespace smtlib {
	namespace ast {
        /* ===================================== Command ====================================== */
        /**
         * Abstract root of the hierarchy of commands
         */
        class Command : public AstNode {
        };

        /* ================================== AssertCommand =================================== */
        /**
         * An 'assert' command containing a term.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class AssertCommand : public Command {
        private:
            std::shared_ptr<Term> term;

        public:
            /**
             * \param term  Asserted term
             */
            AssertCommand(std::shared_ptr<Term> term) : term(term) { }

            const std::shared_ptr<Term> getTerm() const;
            std::shared_ptr<Term> getTerm();

            void setTerm(std::shared_ptr<Term> term);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================= CheckSatCommand ================================== */
        /**
         * A 'check-sat' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class CheckSatCommand : public Command {
        public:
            CheckSatCommand() { }

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =============================== CheckSatAssumCommand =============================== */
        /**
         * A 'check-sat-assuming' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class CheckSatAssumCommand : public Command {
        private:
            std::vector<std::shared_ptr<PropLiteral>> assumptions;

        public:
            /**
             * \param assumptions   List of assumptions
             */
            CheckSatAssumCommand(const std::vector<std::shared_ptr<PropLiteral>> &assumptions);

            const std::vector<std::shared_ptr<PropLiteral>> &getAssumptions() const;
            std::vector<std::shared_ptr<PropLiteral>> &getAssumptions();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =============================== DeclareConstCommand ================================ */
        /**
         * A 'declare-const' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DeclareConstCommand : public Command {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<Sort> sort;
        public:
            /**
             * \param name  Name of the constant
             * \param sort  Sort of the constant
             */
            DeclareConstCommand(std::shared_ptr<Symbol> symbol, std::shared_ptr<Sort> sort)
                    : symbol(symbol), sort(sort) { }

            const std::shared_ptr<Symbol> getSymbol() const;
            std::shared_ptr<Symbol> getSymbol();

            void setSymbol(std::shared_ptr<Symbol> symbol);

            const std::shared_ptr<Sort> getSort() const;
            std::shared_ptr<Sort> getSort();

            void setSort(std::shared_ptr<Sort> sort);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================ DeclareFunCommand ================================= */
        /**
         * A 'declare-fun' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DeclareFunCommand : public Command {
        private:
            std::shared_ptr<Symbol> symbol;
            std::vector<std::shared_ptr<Sort>> params;
            std::shared_ptr<Sort> sort;
        public:
            /**
             * \param name      Name of the function
             * \param params    Sorts of the parameters
             * \param sort      Sort of the return value
             */
            DeclareFunCommand(std::shared_ptr<Symbol> symbol,
                              const std::vector<std::shared_ptr<Sort>> &params,
                              std::shared_ptr<Sort> sort);

            const std::shared_ptr<Symbol> getSymbol() const;
            std::shared_ptr<Symbol> getSymbol();

            void setSymbol(std::shared_ptr<Symbol> symbol);

            const std::vector<std::shared_ptr<Sort>> &getParams() const;
            std::vector<std::shared_ptr<Sort>> &getParams();

            const std::shared_ptr<Sort> getSort() const;
            std::shared_ptr<Sort> getSort();

            void setSort(std::shared_ptr<Sort> sort);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================ DeclareSortCommand ================================ */
        /**
         * A 'declare-sort' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DeclareSortCommand : public Command {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<NumeralLiteral> arity;
        public:
            /**
             * \param name      Name of the sort
             * \param arity     Arity of the sort
             */
            DeclareSortCommand(std::shared_ptr<Symbol> symbol,
                               std::shared_ptr<NumeralLiteral> arity)
                    : symbol(symbol), arity(arity) { }

            const std::shared_ptr<Symbol> getSymbol() const;
            std::shared_ptr<Symbol> getSymbol();

            void setSymbol(std::shared_ptr<Symbol> symbol);

            const std::shared_ptr<NumeralLiteral> getArity() const;
            std::shared_ptr<NumeralLiteral> getArity();

            void setArity(std::shared_ptr<NumeralLiteral> arity);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================= DefineFunCommand ================================= */
        /**
         * A 'define-fun' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DefineFunCommand : public Command {
        private:
            std::shared_ptr<FunctionDefinition> definition;
        public:
            /**
             * \param definition    Function definition
             */
            DefineFunCommand(std::shared_ptr<FunctionDefinition> definition)
                    : definition(definition) { }

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            DefineFunCommand(std::shared_ptr<FunctionDeclaration> signature,
                             std::shared_ptr<Term> body);

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            DefineFunCommand(std::shared_ptr<Symbol> symbol,
                             const  std::vector<std::shared_ptr<SortedVariable>> &params,
                             std::shared_ptr<Sort> sort,
                             std::shared_ptr<Term> body);

            const std::shared_ptr<FunctionDefinition> getDefinition() const;
            std::shared_ptr<FunctionDefinition> getDefinition();

            void setDefinition(std::shared_ptr<FunctionDefinition> definition);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================ DefineFunRecCommand =============================== */
        /**
         * A 'define-fun-rec' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DefineFunRecCommand : public Command {
        private:
            std::shared_ptr<FunctionDefinition> definition;
        public:
            /**
             * \param definition    Function definition
             */
            DefineFunRecCommand(std::shared_ptr<FunctionDefinition> definition)
                    : definition(definition) { }

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            DefineFunRecCommand(std::shared_ptr<FunctionDeclaration> signature,
                                std::shared_ptr<Term> body);

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            DefineFunRecCommand(std::shared_ptr<Symbol> symbol,
                                const std::vector<std::shared_ptr<SortedVariable>> &params,
                                std::shared_ptr<Sort> sort,
                                std::shared_ptr<Term> body);

            const std::shared_ptr<FunctionDefinition> getDefinition() const;
            std::shared_ptr<FunctionDefinition> getDefinition();

            void setDefinition(std::shared_ptr<FunctionDefinition> definition);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =============================== DefineFunsRecCommand =============================== */
        /**
         * A 'define-funs-rec' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DefineFunsRecCommand : public Command {
        private:
            std::vector<std::shared_ptr<FunctionDeclaration>> declarations;
            std::vector<std::shared_ptr<Term>> bodies;
        public:
            /**
             * \param declarations    Function declarations
             * \param bodies          Function bodies
             */
            DefineFunsRecCommand(const std::vector<std::shared_ptr<FunctionDeclaration>> &declarations,
                                 const std::vector<std::shared_ptr<Term>> &bodies);

            const std::vector<std::shared_ptr<FunctionDeclaration>> &getDeclarations() const;
            std::vector<std::shared_ptr<FunctionDeclaration>> &getDeclarations();

            const std::vector<std::shared_ptr<Term>> &getBodies() const;
            std::vector<std::shared_ptr<Term>> &getBodies();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================ DefineSortCommand ================================= */
        /**
         * A 'define-sort' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DefineSortCommand : public Command {
        private:
            std::shared_ptr<Symbol> symbol;
            std::vector<std::shared_ptr<Symbol>> params;
            std::shared_ptr<Sort> sort;
        public:
            /**
             * \param name      Name of the sort
             * \param arity     Arity of the sort
             */
            DefineSortCommand(std::shared_ptr<Symbol> symbol,
                              const std::vector<std::shared_ptr<Symbol>> &params,
                              std::shared_ptr<Sort> sort);

            const std::shared_ptr<Symbol> getSymbol() const;
            std::shared_ptr<Symbol> getSymbol();

            void setSymbol(std::shared_ptr<Symbol> symbol);

            const std::vector<std::shared_ptr<Symbol>> &getParams() const;
            std::vector<std::shared_ptr<Symbol>> &getParams();

            const std::shared_ptr<Sort> getSort() const;
            std::shared_ptr<Sort> getSort();

            void setSort(std::shared_ptr<Sort> sort);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =================================== EchoCommand ==================================== */
        /**
         * An 'echo' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class EchoCommand : public Command {
        private:
            std::string message;
        public:
            /**
             * \param   Message to print
             */
            EchoCommand(std::string message) : message(message) {}

            const std::string &getMessage() const;
            std::string &getMessage();

            void setMessage(std::string message);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =================================== ExitCommand ==================================== */
        /**
         * An 'exit' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ExitCommand : public Command {
        public:
            ExitCommand() { }

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================ GetAssertsCommand ================================= */
        /**
         * A 'get-assertions' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetAssertsCommand : public Command {
        public:
            GetAssertsCommand() { }

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================ GetAssignsCommand ================================= */
        /**
         * A 'get-assignments' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetAssignsCommand : public Command {
        public:
            GetAssignsCommand() { }

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================== GetInfoCommand ================================== */
        /**
         * A 'get-info' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetInfoCommand : public Command {
        private:
            std::shared_ptr<Keyword> flag;
        public:
            /**
             * \param flag  Flag name
             */
            GetInfoCommand(std::shared_ptr<Keyword> flag) : flag(flag) { }

            const std::shared_ptr<Keyword> getFlag() const;
            std::shared_ptr<Keyword> getFlag();

            void setFlag(std::shared_ptr<Keyword> flag);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================= GetModelCommand ================================== */
        /**
         * A 'get-model' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetModelCommand : public Command {
        public:
            GetModelCommand() { }

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================= GetOptionCommand ================================= */
        /**
         * A 'get-option' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetOptionCommand : public Command {
        private:
            std::shared_ptr<Keyword> option;
        public:
            /**
             * \param option    Option name
             */
            GetOptionCommand(std::shared_ptr<Keyword> option) : option(option) { }

            const std::shared_ptr<Keyword> getOption() const;
            std::shared_ptr<Keyword> getOption();

            void setOption(std::shared_ptr<Keyword> option);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================= GetProofCommand ================================== */
        /**
         * A 'get-proof' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetProofCommand : public Command {
        public:
            GetProofCommand() { }

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ============================== GetUnsatAssumsCommand =============================== */
        /**
         * A 'get-unsat-assumptions' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetUnsatAssumsCommand : public Command {
        public:
            GetUnsatAssumsCommand() { }

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =============================== GetUnsatCoreCommand ================================ */
        /**
         * A 'get-unsat-core' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetUnsatCoreCommand : public Command {
        public:
            GetUnsatCoreCommand() { }

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================= GetValueCommand ================================== */
        /**
         * A 'get-value' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetValueCommand : public Command {
        private:
            std::vector<std::shared_ptr<Term>> terms;
        public:
            /**
             * \param terms Terms to evaluate
             */
            GetValueCommand(const std::vector<std::shared_ptr<Term>> &terms);

            const std::vector<std::shared_ptr<Term>> getTerms() const;

            std::vector<std::shared_ptr<Term>> &getTerms();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ==================================== PopCommand ==================================== */
        /**
         * A 'push' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class PopCommand : public Command {
        private:
            std::shared_ptr<NumeralLiteral> numeral;
        public:
            PopCommand(std::shared_ptr<NumeralLiteral> numeral) : numeral(numeral) { }

            const std::shared_ptr<NumeralLiteral> getNumeral() const;
            std::shared_ptr<NumeralLiteral> getNumeral();

            void setNumeral(std::shared_ptr<NumeralLiteral> numeral);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =================================== PushCommand ==================================== */
        /**
         * A 'push' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class PushCommand : public Command {
        private:
            std::shared_ptr<NumeralLiteral> numeral;
        public:
            PushCommand(std::shared_ptr<NumeralLiteral> numeral) : numeral(numeral) { }

            const std::shared_ptr<NumeralLiteral> getNumeral() const;
            std::shared_ptr<NumeralLiteral> getNumeral();

            void setNumeral(std::shared_ptr<NumeralLiteral> numeral);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =================================== ResetCommand =================================== */
        /**
         * A 'reset' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ResetCommand : public Command {
        public:
            ResetCommand() { }

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =============================== ResetAssertsCommand ================================ */
        /**
         * A 'reset-assertions' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ResetAssertsCommand : public Command {
        public:
            ResetAssertsCommand() { }

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================== SetInfoCommand ================================== */
        /**
         * A 'set-info' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SetInfoCommand : public Command {
        private:
            std::shared_ptr<Attribute> info;
        public:
            /**
             * \param info    Info to set
             */
            SetInfoCommand(std::shared_ptr<Attribute> info) : info(info) { }

            const std::shared_ptr<Attribute> getInfo() const;
            std::shared_ptr<Attribute> getInfo();

            void setInfo(std::shared_ptr<Attribute> info);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================= SetLogicCommand ================================== */
        /**
         * A 'set-logic' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SetLogicCommand : public Command {
        private:
            std::shared_ptr<Symbol> logic;
        public:
            /**
             * \param name  Name of the logic to set
             */
            SetLogicCommand(std::shared_ptr<Symbol> logic) : logic(logic) { }

            const std::shared_ptr<Symbol> getLogic() const;
            std::shared_ptr<Symbol> getLogic();

            void setLogic(std::shared_ptr<Symbol> logic);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ================================= SetOptionCommand ================================= */
        /**
         * A 'set-option' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SetOptionCommand : public Command {
        private:
            std::shared_ptr<Attribute> option;
        public:
            /**
             * \param option    Option to set
             */
            SetOptionCommand(std::shared_ptr<Attribute> option) : option(option) { }

            const std::shared_ptr<Attribute> getOption() const;
            std::shared_ptr<Attribute> getOption();

            void setOption(std::shared_ptr<Attribute> option);

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };
    }
}

#endif //PARSE_SMTLIB_AST_COMMAND_H