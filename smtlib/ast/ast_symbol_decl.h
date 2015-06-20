/**
 * \file smt_symbol_decl.h
 * \brief SMT-LIB sort and function symbol declarations.
 */

#ifndef PARSE_SMTLIB_AST_SYMBOL_DECL_H
#define PARSE_SMTLIB_AST_SYMBOL_DECL_H

#include <memory>
#include <vector>
#include "ast_abstract.h"
#include "ast_attribute.h"
#include "ast_basic.h"
#include "ast_identifier.h"
#include "ast_interfaces.h"
#include "ast_sort.h"
#include "ast_literal.h"

namespace smtlib {
    namespace ast {
        /* =============================== SortSymbolDeclaration ============================== */
        /**
         * Declaration of a sort symbol.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as an attribute value.
         */
        class SortSymbolDeclaration : public virtual AstNode,
                                      public AttributeValue {
        private:
            std::shared_ptr<Identifier> identifier;
            std::shared_ptr<NumeralLiteral> arity;
            std::vector<std::shared_ptr<Attribute>> attributes;
        public:
            /**
             * Constructs declaration without attributes.
             * \param identifier    Sort symbol identiier
             * \param arity         Sort arity
             */
            SortSymbolDeclaration(std::shared_ptr<Identifier> identifier,
                                  std::shared_ptr<NumeralLiteral> arity)
                    : identifier(identifier), arity(arity) { }

            /**
             * Constructs declaration with attributes.
             * \param identifier    Sort symbol identiier
             * \param arity         Sort arity
             * \param attributes    Sort symbol declaration attributes
             */
            SortSymbolDeclaration(std::shared_ptr<Identifier> identifier,
                                  std::shared_ptr<NumeralLiteral> arity,
                                  const std::vector<std::shared_ptr<Attribute>> &attributes);

            const std::shared_ptr<Identifier> getIdentifier() const;
            std::shared_ptr<Identifier> getIdentifier();

            void setIdentifier(std::shared_ptr<Identifier> identifier);

            const std::shared_ptr<NumeralLiteral> getArity() const;
            std::shared_ptr<NumeralLiteral> getArity();

            void setArity(std::shared_ptr<NumeralLiteral> arity);

            const std::vector<std::shared_ptr<Attribute>> &getAttributes() const;
            std::vector<std::shared_ptr<Attribute>> &getAttributes();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =============================== FunSymbolDeclaration =============================== */
        /**
         * Abstract class for a function symbol declaration.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as an attribute value.
         */
        class FunSymbolDeclaration : public virtual AstNode,
                                     public AttributeValue {
        };

        /* ============================= SpecConstFunDeclaration ============================== */
        /**
         * Specification constant function symbol declaration.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as an attribute value.
         */
        class SpecConstFunDeclaration : public FunSymbolDeclaration {
        private:
            std::shared_ptr<SpecConstant> constant;
            std::shared_ptr<Sort> sort;
            std::vector<std::shared_ptr<Attribute>> attributes;

        public:
            /**
            * Constructs declaration without attributes.
            * \param constant      Specification constant
            * \param sort          Function sort
            */
            SpecConstFunDeclaration(std::shared_ptr<SpecConstant> constant,
                                    std::shared_ptr<Sort> sort)
                    : constant(constant), sort(sort) { }

            /**
             * Constructs declaration with attributes.
             * \param constant      Specification constant
             * \param sort          Function sort
             * \param attributes    Function symbol declaration attributes
             */
            SpecConstFunDeclaration(std::shared_ptr<SpecConstant> constant,
                                    std::shared_ptr<Sort> sort,
                                    const std::vector<std::shared_ptr<Attribute>> &attributes);

            const std::shared_ptr<SpecConstant> getConstant() const;
            std::shared_ptr<SpecConstant> getConstant();

            void setConstant(std::shared_ptr<SpecConstant> constant);

            const std::shared_ptr<Sort> getSort() const;
            std::shared_ptr<Sort> getSort();

            void setSort(std::shared_ptr<Sort> sort);

            const std::vector<std::shared_ptr<Attribute>> &getAttributes() const;
            std::vector<std::shared_ptr<Attribute>> &getAttributes();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ========================== MetaSpecConstFunDeclaration =========================== */

        /**
         * Meta specification constant function symbol declaration.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as an attribute value.
         */
        class MetaSpecConstFunDeclaration : public FunSymbolDeclaration {
        private:
            std::shared_ptr<MetaSpecConstant> constant;
            std::shared_ptr<Sort> sort;
            std::vector<std::shared_ptr<Attribute>> attributes;

        public:
            /**
            * Constructs declaration without attributes.
            * \param constant      Meta specification constant
            * \param sort          Function sort
            */
            MetaSpecConstFunDeclaration(std::shared_ptr<MetaSpecConstant> constant,
                                        std::shared_ptr<Sort> sort)
                    : constant(constant), sort(sort) { }

            /**
             * Constructs declaration with attributes.
             * \param constant      Meta specification constant
             * \param sort          Function sort
             * \param attributes    Function symbol declaration attributes
             */
            MetaSpecConstFunDeclaration(std::shared_ptr<MetaSpecConstant> constant,
                                        std::shared_ptr<Sort> sort,
                                        const std::vector<std::shared_ptr<Attribute>> &attributes);

            const std::shared_ptr<MetaSpecConstant> getConstant() const;
            std::shared_ptr<MetaSpecConstant> getConstant();

            void setConstant(std::shared_ptr<MetaSpecConstant> constant);

            const std::shared_ptr<Sort> getSort() const;
            std::shared_ptr<Sort> getSort();

            void setSort(std::shared_ptr<Sort> sort);

            const std::vector<std::shared_ptr<Attribute>> &getAttributes() const;
            std::vector<std::shared_ptr<Attribute>> &getAttributes();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* ============================== IdentifierFunDeclaration =============================== */

        /**
         * Identifier function symbol declaration.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as an attribute value.
         */
        class IdentifierFunDeclaration : public FunSymbolDeclaration {
        protected:
            std::shared_ptr<Identifier> identifier;
            std::vector<std::shared_ptr<Sort>> signature;
            std::vector<std::shared_ptr<Attribute>> attributes;

            IdentifierFunDeclaration() { }

        public:
            /**
             * Constructs declaration without attributes.
             * \param identifier    Function identifier
             * \param signature     Function signature
             */
            IdentifierFunDeclaration(std::shared_ptr<Identifier> identifier,
                                  const std::vector<std::shared_ptr<Sort>> &signature);

            /**
             * Constructs declaration with attributes.
             * \param identifier    Function identifier
             * \param signature     Function signature
             * \param attributes    Function symbol declaration attributes
             */
            IdentifierFunDeclaration(std::shared_ptr<Identifier> identifier,
                                  const std::vector<std::shared_ptr<Sort>> &signature,
                                  const std::vector<std::shared_ptr<Attribute>> &attributes);

            const std::shared_ptr<Identifier> getIdentifier() const;
            std::shared_ptr<Identifier> getIdentifier();

            void setIdentifier(std::shared_ptr<Identifier> identifier);

            const std::vector<std::shared_ptr<Sort>> &getSignature() const;
            std::vector<std::shared_ptr<Sort>> &getSignature();

            const std::vector<std::shared_ptr<Attribute>> &getAttributes() const;
            std::vector<std::shared_ptr<Attribute>> &getAttributes();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };

        /* =============================== ParametricFunDeclaration ================================ */

        /**
        * Parametric function symbol declaration.
        * Node of the SMT-LIB abstract syntax tree.
        * Can act as an attribute value.
        */
        class ParametricFunDeclaration : public IdentifierFunDeclaration {
        private:
            std::vector<std::shared_ptr<Symbol>> params;

        public:
            /**
             * Constructs declaration without attributes.
             * \param params        Function parameters
             * \param identifier    Function identifier
             * \param signature     Function signature
             */
            ParametricFunDeclaration(const std::vector<std::shared_ptr<Symbol>> &params,
                                std::shared_ptr<Identifier> identifier,
                                const std::vector<std::shared_ptr<Sort>> &signature);

            /**
             * Constructs declaration with attributes.
             * \param params        Function parameters
             * \param identifier    Function identifier
             * \param signature     Function signature
             * \param attributes    Function symbol declaration attributes
             */
            ParametricFunDeclaration(const std::vector<std::shared_ptr<Symbol>> &params,
                                std::shared_ptr<Identifier> identifier,
                                const std::vector<std::shared_ptr<Sort>> &signature,
                                const std::vector<std::shared_ptr<Attribute>> &attributes);

            const std::vector<std::shared_ptr<Symbol>> &getParams() const;
            std::vector<std::shared_ptr<Symbol>> &getParams();

            virtual void accept(AstVisitor0* visitor) const;

            virtual std::string toString() const;
        };
    }
}

#endif //PARSE_SMTLIB_AST_SYMBOL_DECL_H