/**
 * \file smt_fun.h
 * \brief Function declaration and definition.
 */

#ifndef PARSE_SMTLIB_SMT_FUN_H
#define PARSE_SMTLIB_SMT_FUN_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_basic.h"
#include "smt_interfaces.h"
#include "smt_sort.h"
#include "smt_var.h"

namespace smt {
    /* =============================== FunctionDeclaration ================================ */
    /**
     * An SMT-LIB function declaration.
     * Node of the SMT-LIB abstract syntax tree.
     */
    class FunctionDeclaration : public SmtAstNode {
    private:
        std::shared_ptr<Symbol> symbol;
        std::vector<std::shared_ptr<SortedVariable>> params;
        std::shared_ptr<Sort> type;
    public:
        /**
         * Constructor
         * \param symbol    Name of the function
         * \param params    List of parameters
         * \param type      Return type of the function
         */
        FunctionDeclaration(std::shared_ptr<Symbol> symbol,
                            std::vector<std::shared_ptr<SortedVariable>> &params,
                            std::shared_ptr<Sort> type);

        std::shared_ptr<Symbol> getSymbol();
        void setSymbol(std::shared_ptr<Symbol> symbol);

        std::vector<std::shared_ptr<SortedVariable>> &getParams();

        std::shared_ptr<Sort> getType();
        void setType(std::shared_ptr<Sort> type);

        virtual std::string toString();
    };

    /* ================================ FunctionDefinition ================================ */
    /**
     * An SMT-LIB function definition.
     * Node of the SMT-LIB abstract syntax tree.
     */
    class FunctionDefinition : public SmtAstNode {
    private:
        std::shared_ptr<FunctionDeclaration> signature;
        std::shared_ptr<ITerm> body;
    public:
        /**
         * Constructor
         * \param signature    Function signature
         * \param body      Function body
         */
        FunctionDefinition(std::shared_ptr<FunctionDeclaration> signature,
                           std::shared_ptr<ITerm> body);

        /**
         * Constructor
         * \param symbol    Name of the function
         * \param params    List of parameters
         * \param type      Return type of the function
         * \param body      Function body
         */
        FunctionDefinition(std::shared_ptr<Symbol> symbol,
                           std::vector<std::shared_ptr<SortedVariable>> &params,
                           std::shared_ptr<Sort> type,
                           std::shared_ptr<ITerm> body);

        std::shared_ptr<FunctionDeclaration> getSignature();
        void setSignature(std::shared_ptr<FunctionDeclaration> signature);

        std::shared_ptr<ITerm> getBody();
        void setBody(std::shared_ptr<ITerm> body);
    };
}

#endif //PARSE_SMTLIB_SMT_FUN_H