/**
 * \file smt_symbol_decl.h
 * \brief SMT-LIB sort and function symbol declarations.
 */

#ifndef PARSE_SMTLIB_AST_SYMBOL_DECL_H
#define PARSE_SMTLIB_AST_SYMBOL_DECL_H

#include "ast_abstract.h"
#include "ast_attribute.h"
#include "ast_basic.h"
#include "ast_identifier.h"
#include "ast_interfaces.h"
#include "ast_literal.h"
#include "ast_sort.h"

#include <memory>
#include <vector>

namespace smtlib {
    namespace ast {
        /* =============================== SortSymbolDeclaration ============================== */
        /**
         * Declaration of a sort symbol.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as an attribute value.
         */
        class SortSymbolDeclaration : public virtual AstNode,
                                      public AttributeValue,
                                      public std::enable_shared_from_this<SortSymbolDeclaration> {
        private:
            std::shared_ptr<SimpleIdentifier> identifier;
            std::shared_ptr<NumeralLiteral> arity;
            std::vector<std::shared_ptr<Attribute>> attributes;
        public:
            /**
             * Constructs declaration without attributes.
             * \param identifier    Sort symbol identiier
             * \param arity         Sort arity
             */
            SortSymbolDeclaration(std::shared_ptr<SimpleIdentifier> identifier,
                                  std::shared_ptr<NumeralLiteral> arity)
                    : identifier(identifier), arity(arity) { }

            /**
             * Constructs declaration with attributes.
             * \param identifier    Sort symbol identiier
             * \param arity         Sort arity
             * \param attributes    Sort symbol declaration attributes
             */
            SortSymbolDeclaration(std::shared_ptr<SimpleIdentifier> identifier,
                                  std::shared_ptr<NumeralLiteral> arity,
                                  std::vector<std::shared_ptr<Attribute>>& attributes);

            std::shared_ptr<SimpleIdentifier> getIdentifier();

            void setIdentifier(std::shared_ptr<SimpleIdentifier> identifier);

            std::shared_ptr<NumeralLiteral> getArity();

            void setArity(std::shared_ptr<NumeralLiteral> arity);

            std::vector<std::shared_ptr<Attribute>>& getAttributes();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
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
        class SpecConstFunDeclaration : public FunSymbolDeclaration,
                                        public std::enable_shared_from_this<SpecConstFunDeclaration> {
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
                                    std::vector<std::shared_ptr<Attribute>>& attributes);

            std::shared_ptr<SpecConstant> getConstant();

            void setConstant(std::shared_ptr<SpecConstant> constant);

            std::shared_ptr<Sort> getSort();

            void setSort(std::shared_ptr<Sort> sort);

            std::vector<std::shared_ptr<Attribute>>& getAttributes();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ========================== MetaSpecConstFunDeclaration =========================== */

        /**
         * Meta specification constant function symbol declaration.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as an attribute value.
         */
        class MetaSpecConstFunDeclaration
                : public FunSymbolDeclaration, public std::enable_shared_from_this<MetaSpecConstFunDeclaration> {
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
                                        std::vector<std::shared_ptr<Attribute>>& attributes);

            std::shared_ptr<MetaSpecConstant> getConstant();

            void setConstant(std::shared_ptr<MetaSpecConstant> constant);

            std::shared_ptr<Sort> getSort();

            void setSort(std::shared_ptr<Sort> sort);

            std::vector<std::shared_ptr<Attribute>>& getAttributes();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* ============================== SimpleFunDeclaration =============================== */

        /**
         * Identifier function symbol declaration.
         * Node of the SMT-LIB abstract syntax tree.
         * Can act as an attribute value.
         */
        class SimpleFunDeclaration : public FunSymbolDeclaration,
                                     public std::enable_shared_from_this<SimpleFunDeclaration> {
        protected:
            std::shared_ptr<SimpleIdentifier> identifier;
            std::vector<std::shared_ptr<Sort>> signature;
            std::vector<std::shared_ptr<Attribute>> attributes;

            SimpleFunDeclaration() { }

        public:
            /**
             * Constructs declaration without attributes.
             * \param identifier    Function identifier
             * \param signature     Function signature
             */
            SimpleFunDeclaration(std::shared_ptr<SimpleIdentifier> identifier,
                                 std::vector<std::shared_ptr<Sort>>& signature);

            /**
             * Constructs declaration with attributes.
             * \param identifier    Function identifier
             * \param signature     Function signature
             * \param attributes    Function symbol declaration attributes
             */
            SimpleFunDeclaration(std::shared_ptr<SimpleIdentifier> identifier,
                                 std::vector<std::shared_ptr<Sort>>& signature,
                                 std::vector<std::shared_ptr<Attribute>>& attributes);

            std::shared_ptr<SimpleIdentifier> getIdentifier();

            void setIdentifier(std::shared_ptr<SimpleIdentifier> identifier);

            std::vector<std::shared_ptr<Sort>>& getSignature();

            std::vector<std::shared_ptr<Attribute>>& getAttributes();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };

        /* =============================== ParametricFunDeclaration ================================ */

        /**
        * Parametric function symbol declaration.
        * Node of the SMT-LIB abstract syntax tree.
        * Can act as an attribute value.
        */
        class ParametricFunDeclaration : public FunSymbolDeclaration,
                                         public std::enable_shared_from_this<ParametricFunDeclaration> {
        private:
            std::vector<std::shared_ptr<Symbol>> params;
            std::shared_ptr<SimpleIdentifier> identifier;
            std::vector<std::shared_ptr<Sort>> signature;
            std::vector<std::shared_ptr<Attribute>> attributes;

        public:
            /**
             * Constructs declaration without attributes.
             * \param params        Function parameters
             * \param identifier    Function identifier
             * \param signature     Function signature
             */
            ParametricFunDeclaration(std::vector<std::shared_ptr<Symbol>>& params,
                                     std::shared_ptr<SimpleIdentifier> identifier,
                                     std::vector<std::shared_ptr<Sort>>& signature);

            /**
             * Constructs declaration with attributes.
             * \param params        Function parameters
             * \param identifier    Function identifier
             * \param signature     Function signature
             * \param attributes    Function symbol declaration attributes
             */
            ParametricFunDeclaration(std::vector<std::shared_ptr<Symbol>>& params,
                                     std::shared_ptr<SimpleIdentifier> identifier,
                                     std::vector<std::shared_ptr<Sort>>& signature,
                                     std::vector<std::shared_ptr<Attribute>>& attributes);

            std::vector<std::shared_ptr<Symbol>>& getParams();

            std::shared_ptr<SimpleIdentifier> getIdentifier();

            void setIdentifier(std::shared_ptr<SimpleIdentifier> identifier);

            std::vector<std::shared_ptr<Sort>>& getSignature();

            std::vector<std::shared_ptr<Attribute>>& getAttributes();

            virtual void accept(AstVisitor0* visitor);

            virtual std::string toString();
        };
    }
}

#endif //PARSE_SMTLIB_AST_SYMBOL_DECL_H
