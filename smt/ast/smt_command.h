/**
 * \file smt_command.h
 * \brief SMT-LIB commands that appear in a query file.
 */

#ifndef PARSE_SMTLIB_SMT_COMMAND_H
#define PARSE_SMTLIB_SMT_COMMAND_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_interfaces.h"
#include "smt_basic.h"
#include "smt_sort.h"
#include "smt_literal.h"
#include "smt_fun.h"
#include "smt_attribute.h"

namespace smt {
	namespace ast {
        /* ===================================== Command ====================================== */
        /**
         * Abstract root of the hierarchy of commands
         */
        class Command : public SmtAstNode {
        };

        /* ================================== AssertCommand =================================== */
        /**
         * An 'assert' command containing a term.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class AssertCommand : public Command {
        private:
            std::shared_ptr<ITerm> term;

        public:
            /**
             * \param term  Asserted term
             */
            AssertCommand(std::shared_ptr<ITerm> term);

            std::shared_ptr<ITerm> getTerm();
            void setTerm(std::shared_ptr<ITerm> term);

            virtual std::string toString();
        };

        /* ================================= CheckSatCommand ================================== */
        /**
         * A 'check-sat' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class CheckSatCommand : public Command {
        public:
            CheckSatCommand() { }

            virtual std::string toString();
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
            CheckSatAssumCommand(std::vector<std::shared_ptr<PropLiteral>> &assumptions);

            std::vector<std::shared_ptr<PropLiteral>> &getAssumptions();

            virtual std::string toString();
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
            DeclareConstCommand(std::shared_ptr<Symbol> symbol,
                                std::shared_ptr<Sort> sort);

            std::shared_ptr<Symbol> getSymbol();
            void setSymbol(std::shared_ptr<Symbol> symbol);

            std::shared_ptr<Sort> getSort();
            void setSort(std::shared_ptr<Sort> sort);

            virtual std::string toString();
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
                              std::vector<std::shared_ptr<Sort>> &params,
                              std::shared_ptr<Sort> sort);

            std::shared_ptr<Symbol> getSymbol();
            void setSymbol(std::shared_ptr<Symbol> symbol);

            std::vector<std::shared_ptr<Sort>> &getParams();

            std::shared_ptr<Sort> getSort();
            void setSort(std::shared_ptr<Sort> sort);

            virtual std::string toString();
        };

        /* ================================ DeclareSortCommand ================================ */
        /**
         * A 'declare-sort' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DeclareSortCommand : public Command {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<Symbol> arity;
        public:
            /**
             * \param name      Name of the sort
             * \param arity     Arity of the sort
             */
            DeclareSortCommand(std::shared_ptr<Symbol> symbol,
                               std::shared_ptr<Symbol> arity);

            std::shared_ptr<Symbol> getSymbol();
            void setSymbol(std::shared_ptr<Symbol> symbol);

            std::shared_ptr<Symbol> getArity();
            void setArity(std::shared_ptr<Symbol> arity);

            virtual std::string toString();
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
            DefineFunCommand(std::shared_ptr<FunctionDefinition> definition);

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            DefineFunCommand(std::shared_ptr<FunctionDeclaration> signature,
                             std::shared_ptr<ITerm> body);

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            DefineFunCommand(std::shared_ptr<Symbol> symbol,
                             std::vector<std::shared_ptr<SortedVariable>> &params,
                             std::shared_ptr<Sort> sort,
                             std::shared_ptr<ITerm> body);

            std::shared_ptr<FunctionDefinition> getDefinition();
            void setDefinition(std::shared_ptr<FunctionDefinition> definition);
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
            DefineFunRecCommand(std::shared_ptr<FunctionDefinition> definition);

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            DefineFunRecCommand(std::shared_ptr<FunctionDeclaration> signature,
                                std::shared_ptr<ITerm> body);

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            DefineFunRecCommand(std::shared_ptr<Symbol> symbol,
                                std::vector<std::shared_ptr<SortedVariable>> &params,
                                std::shared_ptr<Sort> sort,
                                std::shared_ptr<ITerm> body);

            std::shared_ptr<FunctionDefinition> getDefinition();
            void setDefinition(std::shared_ptr<FunctionDefinition> definition);
        };

        /* =============================== DefineFunsRecCommand =============================== */
        /**
         * A 'define-funs-rec' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DefineFunsRecCommand : public Command {
        private:
            std::vector<std::shared_ptr<FunctionDefinition>> definitions;
        public:
            /**
             * \param definitions    Function definitions
             */
            DefineFunsRecCommand(std::vector<std::shared_ptr<FunctionDefinition>> &definitions);

            std::vector<std::shared_ptr<FunctionDefinition>> &getDefinitions();
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
                              std::vector<std::shared_ptr<Symbol>> &params,
                              std::shared_ptr<Sort> sort);

            std::shared_ptr<Symbol> getSymbol();
            void setSymbol(std::shared_ptr<Symbol> symbol);

            std::vector<std::shared_ptr<Symbol>> &getParams();

            std::shared_ptr<Sort> getSort();
            void setSort(std::shared_ptr<Sort> sort);
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
            EchoCommand(std::string message);

            std::string &getMessage();
            void setMessage(std::string message);
        };

        /* =================================== ExitCommand ==================================== */
        /**
         * An 'exit' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ExitCommand : public Command {
        public:
            ExitCommand() { }

            virtual std::string toString();
        };

        /* ================================ GetAssertsCommand ================================= */
        /**
         * A 'get-assertions' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetAssertsCommand : public Command {
        public:
            GetAssertsCommand() { }

            virtual std::string toString();
        };

        /* ================================ GetAssignsCommand ================================= */
        /**
         * A 'get-assignments' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetAssignsCommand : public Command {
        public:
            GetAssignsCommand() { }

            virtual std::string toString();
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
            GetInfoCommand(std::shared_ptr<Keyword> flag);

            std::shared_ptr<Keyword> getFlag();
            void setFlag(std::shared_ptr<Keyword> flag);
        };

        /* ================================= GetModelCommand ================================== */
        /**
         * A 'get-model' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetModelCommand : public Command {
        public:
            GetModelCommand() { }

            virtual std::string toString();
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
            GetOptionCommand(std::shared_ptr<Keyword> option);

            std::shared_ptr<Keyword> getOption();
            void setOption(std::shared_ptr<Keyword> option);
        };

        /* ================================= GetProofCommand ================================== */
        /**
         * A 'get-proof' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetProofCommand : public Command {
        public:
            GetProofCommand() { }

            virtual std::string toString();
        };

        /* =============================== GetUnsatCoreCommand ================================ */
        /**
         * A 'get-unsat-core' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetUnsatCoreCommand : public Command {
        public:
            GetUnsatCoreCommand() { }

            virtual std::string toString();
        };

        /* ================================= GetValueCommand ================================== */
        /**
         * A 'get-value' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetValueCommand : public Command {
        private:
            std::vector<std::shared_ptr<ITerm>> terms;
        public:
            /**
             * \param terms Terms to evaluate
             */
            GetValueCommand(std::vector<std::shared_ptr<ITerm>> &terms);

            std::vector<std::shared_ptr<ITerm>> &getTerms();
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
            PopCommand(std::shared_ptr<NumeralLiteral> numeral);

            std::shared_ptr<NumeralLiteral> getNumeral();
            void setNumeral(std::shared_ptr<NumeralLiteral> numeral);

            virtual std::string toString();
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
            PushCommand(std::shared_ptr<NumeralLiteral> numeral);

            std::shared_ptr<NumeralLiteral> getNumeral();
            void setNumeral(std::shared_ptr<NumeralLiteral> numeral);

            virtual std::string toString();
        };

        /* =================================== ResetCommand =================================== */
        /**
         * A 'reset' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ResetCommand : public Command {
        public:
            ResetCommand() { }

            virtual std::string toString();
        };

        /* =============================== ResetAssertsCommand ================================ */
        /**
         * A 'reset-assertions' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ResetAssertsCommand : public Command {
        public:
            ResetAssertsCommand() { }

            virtual std::string toString();
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
            SetInfoCommand(std::shared_ptr<Attribute> info);

            std::shared_ptr<Attribute> getInfo();
            void setInfo(std::shared_ptr<Attribute> info);

            virtual std::string toString();
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
            SetLogicCommand(std::shared_ptr<Symbol> logic);

            std::shared_ptr<Symbol> getLogic();
            void setLogic(std::shared_ptr<Symbol> logic);

            virtual std::string toString();
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
            SetOptionCommand(std::shared_ptr<Attribute> option);

            std::shared_ptr<Attribute> getOption();
            void setOption(std::shared_ptr<Attribute> option);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_SMT_COMMAND_H