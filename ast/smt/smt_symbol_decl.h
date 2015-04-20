/** \file smt_symbol_decl.h
 *  \brief Definition of classes representing sort and function symbol declarations.
 */

#ifndef PARSE_SMTLIB_SMT_SYMBOL_DECL_H
#define PARSE_SMTLIB_SMT_SYMBOL_DECL_H

#include <memory>
#include <vector>
#include "smt_abstract.h"
#include "smt_attribute.h"
#include "smt_basic.h"
#include "smt_interfaces.h"
#include "smt_sort.h"

namespace smt {
    /* =============================== SortSymbolDeclaration ============================== */

    /**
     * Declaration of a sort symbol.
     * Node of the SMT abstract syntax tree.
     * Can act as an attribute value.
     */
    class SortSymbolDeclaration : public virtual SmtAstNode,
                                  public IAttributeValue {
    private:
        std::shared_ptr<IIdentifier> identifier;
        long cardinality;
        std::vector<std::shared_ptr<Attribute>> attributes;
    public:
        /**
         * Constructor without attributes
         * \param identifier    Sort symbol identiier
         * \param cardinality   Sort cardinality
         */
        SortSymbolDeclaration(std::shared_ptr<IIdentifier> identifier,
                              long cardinality);

        /**
         * Constructor with attributes
         * \param identifier    Sort symbol identiier
         * \param cardinality   Sort cardinality
         * \param attributes    Sort symbol declaration attributes
         */
        SortSymbolDeclaration(std::shared_ptr<IIdentifier> identifier,
                              long cardinality,
                              std::vector<std::shared_ptr<Attribute>> &attributes);

        std::shared_ptr<IIdentifier> getIdentifier();
        void setIdentifier(std::shared_ptr<IIdentifier> identifier);

        long getCardinality();
        void setCardinality(long cardinality);

        std::vector<std::shared_ptr<Attribute>> &getAttributes();
    };

    /* =============================== FunSymbolDeclaration =============================== */

    /**
     * Abstract class for a function symbol declaration.
     * Node of the SMT abstract syntax tree.
     * Can act as an attribute value.
     */
    class FunSymbolDeclaration : public virtual SmtAstNode,
                                 public IAttributeValue {  };

    /* ============================= SpecConstFunDeclaration ============================== */

    /**
     * Specification constant function symbol declaration.
     * Node of the SMT abstract syntax tree.
     * Can act as an attribute value.
     */
    class SpecConstFunDeclaration : public FunSymbolDeclaration {
    private:
        std::shared_ptr<ISpecConstant> constant;
        std::shared_ptr<Sort> sort;
        std::vector<std::shared_ptr<Attribute>> attributes;

    public:
        /**
        * Constructor without attributes
        * \param constant      Specification constant
        * \param sort          Function sort
        */
        SpecConstFunDeclaration(std::shared_ptr<ISpecConstant> constant,
                                std::shared_ptr<Sort> sort);

        /**
         * Constructor with attributes
         * \param constant      Specification constant
         * \param sort          Function sort
         * \param attributes    Function symbol declaration attributes
         */
        SpecConstFunDeclaration(std::shared_ptr<ISpecConstant> constant,
                                std::shared_ptr<Sort> sort,
                                std::vector<std::shared_ptr<Attribute>> &attributes);

        std::shared_ptr<ISpecConstant> getConstant();
        void setConstant(std::shared_ptr<ISpecConstant> constant);

        std::shared_ptr<Sort> getSort();
        void setSort(std::shared_ptr<Sort> sort);

        std::vector<std::shared_ptr<Attribute>> &getAttributes();
    };

    /* ========================== MetaSpecConstFunDeclaration =========================== */

    /**
     * Meta specification constant function symbol declaration.
     * Node of the SMT abstract syntax tree.
     * Can act as an attribute value.
     */
    class MetaSpecConstFunDeclaration : public FunSymbolDeclaration {
    private:
        std::shared_ptr<MetaSpecConstant> constant;
        std::shared_ptr<Sort> sort;
        std::vector<std::shared_ptr<Attribute>> attributes;

    public:
        /**
        * Constructor without attributes
        * \param constant      Meta specification constant
        * \param sort          Function sort
        */
        MetaSpecConstFunDeclaration(std::shared_ptr<MetaSpecConstant> constant,
                                    std::shared_ptr<Sort> sort);

        /**
         * Constructor with attributes
         * \param constant      Meta specification constant
         * \param sort          Function sort
         * \param attributes    Function symbol declaration attributes
         */
        MetaSpecConstFunDeclaration(std::shared_ptr<MetaSpecConstant> constant,
                                    std::shared_ptr<Sort> sort,
                                    std::vector<std::shared_ptr<Attribute>> &attributes);

        std::shared_ptr<MetaSpecConstant> getConstant();
        void setConstant(std::shared_ptr<MetaSpecConstant> constant);

        std::shared_ptr<Sort> getSort();
        void setSort(std::shared_ptr<Sort> sort);

        std::vector<std::shared_ptr<Attribute>> &getAttributes();
    };

    /* ============================== IdentifFunDeclaration =============================== */

    /**
     * Identifier function symbol declaration.
     * Node of the SMT abstract syntax tree.
     * Can act as an attribute value.
     */
    class IdentifFunDeclaration : public FunSymbolDeclaration {
    protected:
        std::shared_ptr<IIdentifier> identifier;
        std::vector<std::shared_ptr<Sort>> signature;
        std::vector<std::shared_ptr<Attribute>> attributes;

        IdentifFunDeclaration() { }

    public:
        /**
         * Constructor without attributes
         * \param identifier    Function identifier
         * \param signature     Function signature
         */
        IdentifFunDeclaration(std::shared_ptr<IIdentifier> identifier,
                              std::vector<std::shared_ptr<Sort>> &signature);

        /**
         * Constructor with attributes
         * \param identifier    Function identifier
         * \param signature     Function signature
         * \param attributes    Function symbol declaration attributes
         */
        IdentifFunDeclaration(std::shared_ptr<IIdentifier> identifier,
                              std::vector<std::shared_ptr<Sort>> &signature,
                              std::vector<std::shared_ptr<Attribute>> &attributes);

        std::shared_ptr<IIdentifier> getIdentifier();
        void setIdentifier(std::shared_ptr<IIdentifier> identifier);

        std::vector<std::shared_ptr<Sort>> &getSignature();

        std::vector<std::shared_ptr<Attribute>> &getAttributes();
    };

    /* =============================== ParamFunDeclaration ================================ */

    /**
    * Parametric function symbol declaration.
    * Node of the SMT abstract syntax tree.
    * Can act as an attribute value.
    */
    class ParamFunDeclaration : public IdentifFunDeclaration {
    private:
        std::vector<std::shared_ptr<Symbol>> params;

    public:
        /**
         * Constructor without attributes
         * \param params        Function parameters
         * \param identifier    Function identifier
         * \param signature     Function signature
         */
        ParamFunDeclaration(std::vector<std::shared_ptr<Symbol>> &params,
                            std::shared_ptr<IIdentifier> identifier,
                            std::vector<std::shared_ptr<Sort>> &signature);

        /**
         * Constructor with attributes
         * \param params        Function parameters
         * \param identifier    Function identifier
         * \param signature     Function signature
         * \param attributes    Function symbol declaration attributes
         */
        ParamFunDeclaration(std::vector<std::shared_ptr<Symbol>> &params,
                            std::shared_ptr<IIdentifier> identifier,
                            std::vector<std::shared_ptr<Sort>> &signature,
                            std::vector<std::shared_ptr<Attribute>> &attributes);

        std::vector<std::shared_ptr<Symbol>> &getParams();
    };
};


#endif //PARSE_SMTLIB_SMT_SYMBOL_DECL_H