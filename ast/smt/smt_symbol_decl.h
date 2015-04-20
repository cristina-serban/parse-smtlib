//
// Created by cristinaserban on 17.04.2015.
//

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
    class SortSymbolDeclaration : public virtual SmtAstNode,
                                  public IAttributeValue {
    private:
        std::shared_ptr<IIdentifier> identifier;
        long cardinality;
        std::vector<std::shared_ptr<Attribute>> attributes;
    public:
        SortSymbolDeclaration(std::shared_ptr<IIdentifier> identifier,
                              long cardinality);

        SortSymbolDeclaration(std::shared_ptr<IIdentifier> identifier,
                              long cardinality,
                              std::vector<std::shared_ptr<Attribute>> &attributes);

        std::shared_ptr<IIdentifier> &getIdentifier();
        void setIdentifier(std::shared_ptr<IIdentifier> identifier);

        long getCardinality();
        void setCardinality(long cardinality);

        std::vector<std::shared_ptr<Attribute>> &getAttributes();
    };

    class FunSymbolDeclaration : public virtual SmtAstNode,
                                 public IAttributeValue {  };

    class SpecConstFunDeclaration : FunSymbolDeclaration {
    private:
        std::shared_ptr<ISpecConstant> constant;
        std::shared_ptr<Sort> sort;
        std::vector<std::shared_ptr<Attribute>> attributes;
    public:
        SpecConstFunDeclaration(std::shared_ptr<ISpecConstant> constant,
                                std::shared_ptr<Sort> sort);

        SpecConstFunDeclaration(std::shared_ptr<ISpecConstant> constant,
                                std::shared_ptr<Sort> sort,
                                std::vector<std::shared_ptr<Attribute>> &attributes);

        std::shared_ptr<ISpecConstant> &getConstant();
        void setConstant(std::shared_ptr<ISpecConstant> constant);

        std::shared_ptr<Sort> &getSort();
        void setSort(std::shared_ptr<Sort> sort);

        std::vector<std::shared_ptr<Attribute>> &getAttributes();
    };

    class MetaSpecConstFunDeclaration : public FunSymbolDeclaration {
    private:
        std::shared_ptr<MetaSpecConstant> constant;
        std::shared_ptr<Sort> sort;
        std::vector<std::shared_ptr<Attribute>> attributes;

    public:

        MetaSpecConstFunDeclaration(std::shared_ptr<MetaSpecConstant> constant,
                                    std::shared_ptr<Sort> sort);

        MetaSpecConstFunDeclaration(std::shared_ptr<IIdentifier> identifier,
                                    std::shared_ptr<Sort> sort,
                                    std::vector<std::shared_ptr<Attribute>> &attributes);

        std::shared_ptr<MetaSpecConstant> &getConstant();
        void setConstant(std::shared_ptr<MetaSpecConstant> constant);

        std::shared_ptr<Sort> &getSort();
        void setSort(std::shared_ptr<Sort> sort);

        std::vector<std::shared_ptr<Attribute>> &getAttributes();
    };

    class IdentifFunDeclaration : public FunSymbolDeclaration {
    protected:
        std::shared_ptr<IIdentifier> identifier;
        std::vector<std::shared_ptr<Sort>> signature;
        std::vector<std::shared_ptr<Attribute>> attributes;

        IdentifFunDeclaration();

    public:
        IdentifFunDeclaration(std::shared_ptr<IIdentifier> identifier,
                              std::vector<std::shared_ptr<Sort>> &signature);

        IdentifFunDeclaration(std::shared_ptr<IIdentifier> identifier,
                              std::vector<std::shared_ptr<Sort>> &signature,
                              std::vector<std::shared_ptr<Attribute>> &attributes);

        std::shared_ptr<IIdentifier> &getIdentifier();
        void setIdentifier(std::shared_ptr<IIdentifier> identifier);

        std::vector<std::shared_ptr<Sort>> &getSignature();

        std::vector<std::shared_ptr<Attribute>> &getAttributes();
    };

    class ParamFunDeclaration : public IdentifFunDeclaration {
    private:
        std::vector<std::shared_ptr<Symbol>> params;

    public:
        ParamFunDeclaration(std::vector<std::shared_ptr<Symbol>> &params,
                            std::shared_ptr<IIdentifier> identifier,
                            std::vector<std::shared_ptr<Sort>> &signature);

        ParamFunDeclaration(std::vector<std::shared_ptr<Symbol>> &params,
                            std::shared_ptr<IIdentifier> identifier,
                            std::vector<std::shared_ptr<Sort>> &signature,
                            std::vector<std::shared_ptr<Attribute>> &attributes);

        std::vector<std::shared_ptr<Symbol>> &getParams();
    };
};


#endif //PARSE_SMTLIB_SMT_SYMBOL_DECL_H
