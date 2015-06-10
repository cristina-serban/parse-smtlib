#ifndef PARSE_SMTLIB_AST_CLASSES_H
#define PARSE_SMTLIB_AST_CLASSES_H

namespace smtlib {
    namespace ast {
        class AstNode;

        class Attribute;
        class CompoundAttributeValue;

        class Symbol;
        class Keyword;
        class MetaSpecConstant;
        class BooleanValue;
        class PropLiteral;

        class AssertCommand;
        class CheckSatCommand;
        class CheckSatAssumCommand;
        class DeclareConstCommand;
        class DeclareFunCommand;
        class DeclareSortCommand;
        class DefineFunCommand;
        class DefineFunRecCommand;
        class DefineFunsRecCommand;
        class DefineSortCommand;
        class EchoCommand;
        class ExitCommand;
        class GetAssertsCommand;
        class GetAssignsCommand;
        class GetInfoCommand;
        class GetModelCommand;
        class GetOptionCommand;
        class GetProofCommand;
        class GetUnsatAssumsCommand;
        class GetUnsatCoreCommand;
        class GetValueCommand;
        class PopCommand;
        class PushCommand;
        class ResetCommand;
        class ResetAssertsCommand;
        class SetInfoCommand;
        class SetLogicCommand;
        class SetOptionCommand;

        class FunctionDeclaration;
        class FunctionDefinition;

        class Identifier;
        class QualifiedIdentifier;

        class DecimalLiteral;
        class NumeralLiteral;
        class StringLiteral;

        class Logic;
        class Theory;
        class Script;
        class Sort;

        class CompSExpression;

        class SortSymbolDeclaration;

        class SpecConstFunDeclaration;
        class MetaSpecConstFunDeclaration;
        class IdentifierFunDeclaration;
        class ParametricFunDeclaration;

        class QualifiedTerm;
        class LetTerm;
        class ForallTerm;
        class ExistsTerm;
        class AnnotatedTerm;

        class SortedVariable;
        class VarBinding;
    }
}

#endif //PARSE_SMTLIB_AST_CLASSES_H
