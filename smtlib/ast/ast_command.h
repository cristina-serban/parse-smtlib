/**
 * \file smt_command.h
 * \brief SMT-LIB commands that appear in a query file.
 */

#ifndef PARSE_SMTLIB_AST_COMMAND_H
#define PARSE_SMTLIB_AST_COMMAND_H

#include "ast_abstract.h"
#include "ast_attribute.h"
#include "ast_basic.h"
#include "ast_datatype.h"
#include "ast_interfaces.h"
#include "ast_fun.h"
#include "ast_literal.h"
#include "ast_sort.h"

#include <memory>
#include <vector>

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
        class AssertCommand : public Command,
                              public std::enable_shared_from_this<AssertCommand> {
        private:
            std::shared_ptr<Term> term;

        public:
            /**
             * \param term  Asserted term
             */
            inline AssertCommand(std::shared_ptr<Term> term) : term(term) { }

            inline std::shared_ptr<Term> getTerm() { return term; }

            inline void setTerm(std::shared_ptr<Term> term) { this->term = term; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= CheckSatCommand ================================== */
        /**
         * A 'check-sat' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class CheckSatCommand : public Command,
                                public std::enable_shared_from_this<CheckSatCommand> {
        public:
            inline CheckSatCommand() { }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== CheckSatAssumCommand =============================== */
        /**
         * A 'check-sat-assuming' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class CheckSatAssumCommand : public Command,
                                     public std::enable_shared_from_this<CheckSatAssumCommand> {
        private:
            std::vector<std::shared_ptr<PropLiteral>> assumptions;

        public:
            /**
             * \param assumptions   List of assumptions
             */
            CheckSatAssumCommand(std::vector<std::shared_ptr<PropLiteral>>& assumptions);

            inline std::vector<std::shared_ptr<PropLiteral>>& getAssumptions() { return assumptions; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== DeclareConstCommand ================================ */
        /**
         * A 'declare-const' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DeclareConstCommand : public Command,
                                    public std::enable_shared_from_this<DeclareConstCommand> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<Sort> sort;
        public:
            /**
             * \param name  Name of the constant
             * \param sort  Sort of the constant
             */
            inline DeclareConstCommand(std::shared_ptr<Symbol> symbol, std::shared_ptr<Sort> sort)
                    : symbol(symbol), sort(sort) { }

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::shared_ptr<Sort> getSort() { return sort; }

            inline void setSort(std::shared_ptr<Sort> sort) { this->sort = sort; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ============================== DeclareDatatypeCommand ============================== */
        /**
         * A 'declare-datatype' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DeclareDatatypeCommand : public Command,
                                       public std::enable_shared_from_this<DeclareDatatypeCommand> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<DatatypeDeclaration> declaration;
        public:
            /**
             * \param declaration   Datatype declaration
             */
            inline DeclareDatatypeCommand(std::shared_ptr<Symbol> symbol,
                                          std::shared_ptr<DatatypeDeclaration> declaration)
                    : symbol(symbol), declaration(declaration) { }

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::shared_ptr<DatatypeDeclaration> getDeclaration() { return  declaration; }

            inline void setDeclaration(std::shared_ptr<DatatypeDeclaration> declaration) {
                this->declaration = declaration;
            }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ============================= DeclareDatatypesCommand ============================== */
        /**
         * A 'declare-datatypes' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DeclareDatatypesCommand : public Command,
                                        public std::enable_shared_from_this<DeclareDatatypesCommand> {
        private:
            std::vector<std::shared_ptr<SortDeclaration>> sorts;
            std::vector<std::shared_ptr<DatatypeDeclaration>> declarations;
        public:
            /**
             * \param sorts         Names and arities of the new datatypes
             * \param declarations  Declarations of the new datatypes
             */
            DeclareDatatypesCommand(std::vector<std::shared_ptr<SortDeclaration>>& sorts,
                                    std::vector<std::shared_ptr<DatatypeDeclaration>>& declarations);

            inline std::vector<std::shared_ptr<SortDeclaration>>& getSorts() { return sorts; }

            inline std::vector<std::shared_ptr<DatatypeDeclaration>>& getDeclarations() { return declarations; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DeclareFunCommand ================================= */
        /**
         * A 'declare-fun' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DeclareFunCommand : public Command,
                                  public std::enable_shared_from_this<DeclareFunCommand> {
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
                              std::vector<std::shared_ptr<Sort>>& params,
                              std::shared_ptr<Sort> sort);

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::vector<std::shared_ptr<Sort>>& getParams() { return params; }

            inline std::shared_ptr<Sort> getSort() { return sort; }

            inline void setSort(std::shared_ptr<Sort> sort) { this->sort = sort; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DeclareSortCommand ================================ */
        /**
         * A 'declare-sort' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DeclareSortCommand : public Command,
                                   public std::enable_shared_from_this<DeclareSortCommand> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::shared_ptr<NumeralLiteral> arity;
        public:
            /**
             * \param name      Name of the sort
             * \param arity     Arity of the sort
             */
            inline DeclareSortCommand(std::shared_ptr<Symbol> symbol,
                               std::shared_ptr<NumeralLiteral> arity)
                    : symbol(symbol), arity(arity) { }

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::shared_ptr<NumeralLiteral> getArity() { return arity; }

            inline void setArity(std::shared_ptr<NumeralLiteral> arity) { this->arity = arity; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= DefineFunCommand ================================= */
        /**
         * A 'define-fun' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DefineFunCommand : public Command,
                                 public std::enable_shared_from_this<DefineFunCommand> {
        private:
            std::shared_ptr<FunctionDefinition> definition;
        public:
            /**
             * \param definition    Function definition
             */
            inline DefineFunCommand(std::shared_ptr<FunctionDefinition> definition)
                    : definition(definition) { }

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            inline DefineFunCommand(std::shared_ptr<FunctionDeclaration> signature,
                                    std::shared_ptr<Term> body) {
                definition = std::make_shared<FunctionDefinition>(signature, body);
            }

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            DefineFunCommand(std::shared_ptr<Symbol> symbol,
                             std::vector<std::shared_ptr<SortedVariable>>& params,
                             std::shared_ptr<Sort> sort,
                             std::shared_ptr<Term> body);

            inline std::shared_ptr<FunctionDefinition> getDefinition() { return definition; }

            inline void setDefinition(std::shared_ptr<FunctionDefinition> definition) { this->definition = definition; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DefineFunRecCommand =============================== */
        /**
         * A 'define-fun-rec' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DefineFunRecCommand : public Command,
                                    public std::enable_shared_from_this<DefineFunRecCommand> {
        private:
            std::shared_ptr<FunctionDefinition> definition;
        public:
            /**
             * \param definition    Function definition
             */
            inline DefineFunRecCommand(std::shared_ptr<FunctionDefinition> definition)
                    : definition(definition) { }

            /**
             * \param signature    Function signature
             * \param body         Function body
             */
            inline DefineFunRecCommand(std::shared_ptr<FunctionDeclaration> signature,
                                       std::shared_ptr<Term> body) {
                definition = std::make_shared<FunctionDefinition>(signature, body);
            }

            /**
             * \param symbol    Name of the function
             * \param params    List of parameters
             * \param type      Sort of the return value
             * \param body      Function body
             */
            DefineFunRecCommand(std::shared_ptr<Symbol> symbol,
                                std::vector<std::shared_ptr<SortedVariable>>& params,
                                std::shared_ptr<Sort> sort,
                                std::shared_ptr<Term> body);

            inline std::shared_ptr<FunctionDefinition> getDefinition() { return definition; }

            inline void setDefinition(std::shared_ptr<FunctionDefinition> definition) { this->definition = definition; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== DefineFunsRecCommand =============================== */
        /**
         * A 'define-funs-rec' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DefineFunsRecCommand : public Command,
                                     public std::enable_shared_from_this<DefineFunsRecCommand> {
        private:
            std::vector<std::shared_ptr<FunctionDeclaration>> declarations;
            std::vector<std::shared_ptr<Term>> bodies;
        public:
            /**
             * \param declarations    Function declarations
             * \param bodies          Function bodies
             */
            DefineFunsRecCommand(std::vector<std::shared_ptr<FunctionDeclaration>>& declarations,
                                 std::vector<std::shared_ptr<Term>>& bodies);

            inline std::vector<std::shared_ptr<FunctionDeclaration>>& getDeclarations() { return declarations; }

            inline std::vector<std::shared_ptr<Term>>& getBodies() { return bodies; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ DefineSortCommand ================================= */
        /**
         * A 'define-sort' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class DefineSortCommand : public Command,
                                  public std::enable_shared_from_this<DefineSortCommand> {
        private:
            std::shared_ptr<Symbol> symbol;
            std::vector<std::shared_ptr<Symbol>> params;
            std::shared_ptr<Sort> sort;
        public:
            /**
             * \param symbol    Name of the sort
             * \param params    Sort parameters
             * \param sort      Definition of the new sort
             */
            DefineSortCommand(std::shared_ptr<Symbol> symbol,
                              std::vector<std::shared_ptr<Symbol>>& params,
                              std::shared_ptr<Sort> sort);

            inline std::shared_ptr<Symbol> getSymbol() { return symbol; }

            inline void setSymbol(std::shared_ptr<Symbol> symbol) { this->symbol = symbol; }

            inline std::vector<std::shared_ptr<Symbol>>& getParams() { return params; }

            inline std::shared_ptr<Sort> getSort() { return sort; }

            inline void setSort(std::shared_ptr<Sort> sort) { this->sort = sort; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== EchoCommand ==================================== */
        /**
         * An 'echo' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class EchoCommand : public Command,
                            public std::enable_shared_from_this<EchoCommand> {
        private:
            std::string message;
        public:
            /**
             * \param   Message to print
             */
            inline EchoCommand(std::string message) : message(message) { }

            inline std::string &getMessage() { return message; }

            inline void setMessage(std::string message) { this->message = message; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== ExitCommand ==================================== */
        /**
         * An 'exit' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ExitCommand : public Command,
                            public std::enable_shared_from_this<ExitCommand> {
        public:
            inline ExitCommand() { }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ GetAssertsCommand ================================= */
        /**
         * A 'get-assertions' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetAssertsCommand : public Command,
                                  public std::enable_shared_from_this<GetAssertsCommand> {
        public:
            inline GetAssertsCommand() { }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================ GetAssignsCommand ================================= */
        /**
         * A 'get-assignments' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetAssignsCommand : public Command,
                                  public std::enable_shared_from_this<GetAssignsCommand> {
        public:
            inline GetAssignsCommand() { }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================== GetInfoCommand ================================== */
        /**
         * A 'get-info' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetInfoCommand : public Command,
                               public std::enable_shared_from_this<GetInfoCommand> {
        private:
            std::shared_ptr<Keyword> flag;
        public:
            /**
             * \param flag  Flag name
             */
            inline GetInfoCommand(std::shared_ptr<Keyword> flag) : flag(flag) { }

            inline std::shared_ptr<Keyword> getFlag() { return flag; }

            inline void setFlag(std::shared_ptr<Keyword> flag) { this->flag = flag; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= GetModelCommand ================================== */
        /**
         * A 'get-model' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetModelCommand : public Command,
                                public std::enable_shared_from_this<GetModelCommand> {
        public:
            inline GetModelCommand() { }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= GetOptionCommand ================================= */
        /**
         * A 'get-option' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetOptionCommand : public Command,
                                 public std::enable_shared_from_this<GetOptionCommand> {
        private:
            std::shared_ptr<Keyword> option;
        public:
            /**
             * \param option    Option name
             */
            inline GetOptionCommand(std::shared_ptr<Keyword> option) : option(option) { }

            inline std::shared_ptr<Keyword> getOption() { return option; }

            inline void setOption(std::shared_ptr<Keyword> option) { this->option = option; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= GetProofCommand ================================== */
        /**
         * A 'get-proof' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetProofCommand : public Command,
                                public std::enable_shared_from_this<GetProofCommand> {
        public:
            inline GetProofCommand() { }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ============================== GetUnsatAssumsCommand =============================== */
        /**
         * A 'get-unsat-assumptions' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetUnsatAssumsCommand : public Command,
                                      public std::enable_shared_from_this<GetUnsatAssumsCommand> {
        public:
            inline GetUnsatAssumsCommand() { }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== GetUnsatCoreCommand ================================ */
        /**
         * A 'get-unsat-core' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetUnsatCoreCommand : public Command,
                                    public std::enable_shared_from_this<GetUnsatCoreCommand> {
        public:
            inline GetUnsatCoreCommand() { }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= GetValueCommand ================================== */
        /**
         * A 'get-value' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class GetValueCommand : public Command,
                                public std::enable_shared_from_this<GetValueCommand> {
        private:
            std::vector<std::shared_ptr<Term>> terms;
        public:
            /**
             * \param terms Terms to evaluate
             */
            GetValueCommand(std::vector<std::shared_ptr<Term>>& terms);

            inline std::vector<std::shared_ptr<Term>>& getTerms() { return terms; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ==================================== PopCommand ==================================== */
        /**
         * A 'pop' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class PopCommand : public Command,
                           public std::enable_shared_from_this<PopCommand> {
        private:
            std::shared_ptr<NumeralLiteral> numeral;
        public:
            /**
             * \param numeral   Number of levels to pop
             */
            inline PopCommand(std::shared_ptr<NumeralLiteral> numeral) : numeral(numeral) { }

            inline std::shared_ptr<NumeralLiteral> getNumeral() { return numeral; }

            inline void setNumeral(std::shared_ptr<NumeralLiteral> numeral) { this->numeral = numeral; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== PushCommand ==================================== */
        /**
         * A 'push' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class PushCommand : public Command,
                            public std::enable_shared_from_this<PushCommand> {
        private:
            std::shared_ptr<NumeralLiteral> numeral;
        public:
            /**
             * \param numeral   Number of levels to push
             */
            inline PushCommand(std::shared_ptr<NumeralLiteral> numeral) : numeral(numeral) { }

            inline std::shared_ptr<NumeralLiteral> getNumeral() { return numeral; }

            inline void setNumeral(std::shared_ptr<NumeralLiteral> numeral) { this->numeral = numeral; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =================================== ResetCommand =================================== */
        /**
         * A 'reset' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ResetCommand : public Command,
                             public std::enable_shared_from_this<ResetCommand> {
        public:
            inline ResetCommand() { }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== ResetAssertsCommand ================================ */
        /**
         * A 'reset-assertions' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class ResetAssertsCommand : public Command,
                                    public std::enable_shared_from_this<ResetAssertsCommand> {
        public:
            inline ResetAssertsCommand() { }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================== SetInfoCommand ================================== */
        /**
         * A 'set-info' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SetInfoCommand : public Command,
                               public std::enable_shared_from_this<SetInfoCommand> {
        private:
            std::shared_ptr<Attribute> info;
        public:
            /**
             * \param info    Info to set
             */
            inline SetInfoCommand(std::shared_ptr<Attribute> info) : info(info) { }

            inline std::shared_ptr<Attribute> getInfo() { return info; }

            inline void setInfo(std::shared_ptr<Attribute> info) { this->info = info; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= SetLogicCommand ================================== */
        /**
         * A 'set-logic' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SetLogicCommand : public Command,
                                public std::enable_shared_from_this<SetLogicCommand> {
        private:
            std::shared_ptr<Symbol> logic;
        public:
            /**
             * \param name  Name of the logic to set
             */
            inline SetLogicCommand(std::shared_ptr<Symbol> logic) : logic(logic) { }

            inline std::shared_ptr<Symbol> getLogic() { return logic; }

            inline void setLogic(std::shared_ptr<Symbol> logic) { this->logic = logic; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ================================= SetOptionCommand ================================= */
        /**
         * A 'set-option' command.
         * Node of the SMT-LIB abstract syntax tree.
         */
        class SetOptionCommand : public Command,
                                 public std::enable_shared_from_this<SetOptionCommand> {
        private:
            std::shared_ptr<Attribute> option;
        public:
            /**
             * \param option    Option to set
             */
            inline SetOptionCommand(std::shared_ptr<Attribute> option) : option(option) { }

            inline std::shared_ptr<Attribute> getOption() { return option; }

            inline void setOption(std::shared_ptr<Attribute> option) { this->option = option; }

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_COMMAND_H