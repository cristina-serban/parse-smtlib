#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include <unordered_map>
#include "smtlib-glue.h"

#include "../smtlib/parser/smt_parser.h"

#include "../smtlib/ast/ast_attribute.h"
#include "../smtlib/ast/ast_basic.h"
#include "../smtlib/ast/ast_command.h"
#include "../smtlib/ast/ast_fun.h"
#include "../smtlib/ast/ast_identifier.h"
#include "../smtlib/ast/ast_literal.h"
#include "../smtlib/ast/ast_logic.h"
#include "../smtlib/ast/ast_sexp.h"
#include "../smtlib/ast/ast_script.h"
#include "../smtlib/ast/ast_sort.h"
#include "../smtlib/ast/ast_symbol_decl.h"
#include "../smtlib/ast/ast_term.h"
#include "../smtlib/ast/ast_theory.h"
#include "../smtlib/ast/ast_var.h"

using namespace smtlib;
using namespace smtlib::ast;

std::unordered_map<smtlib::ast::AstNode *, std::shared_ptr<smtlib::ast::AstNode>> nodemap;

template<class T>
std::shared_ptr<T> share(SmtPtr nakedPtr) {
    return std::dynamic_pointer_cast<T>(nodemap[nakedPtr]);
}

template<>
std::shared_ptr<SpecConstant> share(SmtPtr nakedPtr) {
    std::shared_ptr<NumeralLiteral> option1 = std::dynamic_pointer_cast<NumeralLiteral>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    std::shared_ptr<DecimalLiteral> option2 = std::dynamic_pointer_cast<DecimalLiteral>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    std::shared_ptr<StringLiteral> option3 = std::dynamic_pointer_cast<StringLiteral>(nodemap[nakedPtr]);
    if (option3) {
        return option3->shared_from_this();
    }

    throw;
}

template<>
std::shared_ptr<Command> share(SmtPtr nakedPtr) {
    std::shared_ptr<AssertCommand> option1 = std::dynamic_pointer_cast<AssertCommand>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    std::shared_ptr<CheckSatCommand> option2 = std::dynamic_pointer_cast<CheckSatCommand>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    std::shared_ptr<CheckSatAssumCommand> option3 = std::dynamic_pointer_cast<CheckSatAssumCommand>(nodemap[nakedPtr]);
    if (option3) {
        return option3->shared_from_this();
    }

    std::shared_ptr<DeclareConstCommand> option4 = std::dynamic_pointer_cast<DeclareConstCommand>(nodemap[nakedPtr]);
    if (option4) {
        return option4->shared_from_this();
    }

    std::shared_ptr<DeclareFunCommand> option5 = std::dynamic_pointer_cast<DeclareFunCommand>(nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    std::shared_ptr<DeclareSortCommand> option6 = std::dynamic_pointer_cast<DeclareSortCommand>(nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    std::shared_ptr<DefineFunCommand> option7 = std::dynamic_pointer_cast<DefineFunCommand>(nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    std::shared_ptr<DefineFunRecCommand> option8 = std::dynamic_pointer_cast<DefineFunRecCommand>(nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    std::shared_ptr<DefineFunsRecCommand> option9 = std::dynamic_pointer_cast<DefineFunsRecCommand>(nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    std::shared_ptr<DefineSortCommand> option10 = std::dynamic_pointer_cast<DefineSortCommand>(nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    std::shared_ptr<EchoCommand> option11 = std::dynamic_pointer_cast<EchoCommand>(nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    std::shared_ptr<ExitCommand> option12 = std::dynamic_pointer_cast<ExitCommand>(nodemap[nakedPtr]);
    if (option12) {
        return option12->shared_from_this();
    }

    std::shared_ptr<SetOptionCommand> option13 = std::dynamic_pointer_cast<SetOptionCommand>(nodemap[nakedPtr]);
    if (option13) {
        return option13->shared_from_this();
    }

    std::shared_ptr<GetAssertsCommand> option14 = std::dynamic_pointer_cast<GetAssertsCommand>(nodemap[nakedPtr]);
    if (option14) {
        return option14->shared_from_this();
    }

    std::shared_ptr<GetAssignsCommand> option15 = std::dynamic_pointer_cast<GetAssignsCommand>(nodemap[nakedPtr]);
    if (option15) {
        return option15->shared_from_this();
    }

    std::shared_ptr<GetInfoCommand> option16 = std::dynamic_pointer_cast<GetInfoCommand>(nodemap[nakedPtr]);
    if (option16) {
        return option16->shared_from_this();
    }

    std::shared_ptr<GetModelCommand> option17 = std::dynamic_pointer_cast<GetModelCommand>(nodemap[nakedPtr]);
    if (option17) {
        return option17->shared_from_this();
    }

    std::shared_ptr<GetOptionCommand> option18 = std::dynamic_pointer_cast<GetOptionCommand>(nodemap[nakedPtr]);
    if (option18) {
        return option18->shared_from_this();
    }

    std::shared_ptr<GetProofCommand> option19 = std::dynamic_pointer_cast<GetProofCommand>(nodemap[nakedPtr]);
    if (option19) {
        return option19->shared_from_this();
    }

    std::shared_ptr<GetUnsatAssumsCommand> option20 = std::dynamic_pointer_cast<GetUnsatAssumsCommand>(nodemap[nakedPtr]);
    if (option20) {
        return option20->shared_from_this();
    }

    std::shared_ptr<GetUnsatCoreCommand> option21 = std::dynamic_pointer_cast<GetUnsatCoreCommand>(nodemap[nakedPtr]);
    if (option21) {
        return option21->shared_from_this();
    }

    std::shared_ptr<GetValueCommand> option22 = std::dynamic_pointer_cast<GetValueCommand>(nodemap[nakedPtr]);
    if (option22) {
        return option22->shared_from_this();
    }

    std::shared_ptr<PopCommand> option23 = std::dynamic_pointer_cast<PopCommand>(nodemap[nakedPtr]);
    if (option23) {
        return option23->shared_from_this();
    }

    std::shared_ptr<PushCommand> option24 = std::dynamic_pointer_cast<PushCommand>(nodemap[nakedPtr]);
    if (option24) {
        return option24->shared_from_this();
    }

    std::shared_ptr<ResetCommand> option25 = std::dynamic_pointer_cast<ResetCommand>(nodemap[nakedPtr]);
    if (option25) {
        return option25->shared_from_this();
    }

    std::shared_ptr<ResetAssertsCommand> option26 = std::dynamic_pointer_cast<ResetAssertsCommand>(nodemap[nakedPtr]);
    if (option26) {
        return option26->shared_from_this();
    }

    std::shared_ptr<SetInfoCommand> option27 = std::dynamic_pointer_cast<SetInfoCommand>(nodemap[nakedPtr]);
    if (option27) {
        return option27->shared_from_this();
    }

    std::shared_ptr<SetLogicCommand> option28 = std::dynamic_pointer_cast<SetLogicCommand>(nodemap[nakedPtr]);
    if (option28) {
        return option28->shared_from_this();
    }

    throw;
}

template<>
std::shared_ptr<FunSymbolDeclaration> share(SmtPtr nakedPtr) {
    std::shared_ptr<SpecConstFunDeclaration> option6 = std::dynamic_pointer_cast<SpecConstFunDeclaration>(nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    std::shared_ptr<MetaSpecConstFunDeclaration> option7 = std::dynamic_pointer_cast<MetaSpecConstFunDeclaration>(nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    std::shared_ptr<IdentifierFunDeclaration> option8 = std::dynamic_pointer_cast<IdentifierFunDeclaration>(nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    std::shared_ptr<ParametricFunDeclaration> option9 = std::dynamic_pointer_cast<ParametricFunDeclaration>(nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    throw;
}

template<>
std::shared_ptr<AttributeValue> share(SmtPtr nakedPtr) {
    std::shared_ptr<BooleanValue> option1 = std::dynamic_pointer_cast<BooleanValue>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    if(dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    std::shared_ptr<SortSymbolDeclaration> option5 = std::dynamic_pointer_cast<SortSymbolDeclaration>(nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    if(dynamic_cast<FunSymbolDeclaration*>(nakedPtr)) {
        return share<FunSymbolDeclaration>(nakedPtr);
    }

    std::shared_ptr<Symbol> option10 = std::dynamic_pointer_cast<Symbol>(nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    std::shared_ptr<CompSExpression> option11 = std::dynamic_pointer_cast<CompSExpression>(nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    std::shared_ptr<CompAttributeValue> option12 = std::dynamic_pointer_cast<CompAttributeValue>(nodemap[nakedPtr]);
    if (option12) {
        return option12->shared_from_this();
    }
    
    throw;
}

template<>
std::shared_ptr<SExpression> share(SmtPtr nakedPtr) {
    if(dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    std::shared_ptr<Symbol> option4 = std::dynamic_pointer_cast<Symbol>(nodemap[nakedPtr]);
    if (option4) {
        return option4->shared_from_this();
    }

    std::shared_ptr<Keyword> option5 = std::dynamic_pointer_cast<Keyword>(nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    std::shared_ptr<CompSExpression> option6 = std::dynamic_pointer_cast<CompSExpression>(nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }
    
    throw;
}

template<>
std::shared_ptr<QIdentifier> share(SmtPtr nakedPtr) {
    std::shared_ptr<Identifier> option1 = std::dynamic_pointer_cast<Identifier>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    std::shared_ptr<QualifiedIdentifier> option2 = std::dynamic_pointer_cast<QualifiedIdentifier>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
std::shared_ptr<Term> share(SmtPtr nakedPtr) {
    if(dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    if(dynamic_cast<QIdentifier*>(nakedPtr)) {
        return share<QIdentifier>(nakedPtr);
    }

    std::shared_ptr<AnnotatedTerm> option6 = std::dynamic_pointer_cast<AnnotatedTerm>(nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    std::shared_ptr<ExistsTerm> option7 = std::dynamic_pointer_cast<ExistsTerm>(nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    std::shared_ptr<ForallTerm> option8 = std::dynamic_pointer_cast<ForallTerm>(nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    std::shared_ptr<LetTerm> option9 = std::dynamic_pointer_cast<LetTerm>(nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    std::shared_ptr<QualifiedTerm> option10 = std::dynamic_pointer_cast<QualifiedTerm>(nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    throw;
}

template<>
std::shared_ptr<Index> share(SmtPtr nakedPtr) {
    std::shared_ptr<NumeralLiteral> option1 = std::dynamic_pointer_cast<NumeralLiteral>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    std::shared_ptr<Symbol> option2 = std::dynamic_pointer_cast<Symbol>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

//namespace smtlib {
    //namespace ast {

        class ParserInternalList {
        private:
            std::vector<SmtPtr> v;
        public:
            template<class T>
            std::vector<std::shared_ptr<T>> unwrap() {
                std::vector<std::shared_ptr<T>> result;
                for (unsigned long i = 0, n = v.size(); i < n; ++i) {
                    result.push_back(share<T>(v[i]));
                }
                v.clear();
                return result;
            };

            inline void add(SmtPtr item) {
                v.push_back(item);
            }
        };
    //}
//}

SmtList smt_listCreate() {
    return new ParserInternalList();
}

void smt_listAdd(SmtList list, SmtPtr item) {
    list->add(item);
}

void smt_listDelete(SmtList list) {
    delete list;
}

void smt_print(SmtPtr ptr) {
    std::cout << ptr->toString();
}

void smt_setAst(SmtPrsr parser, SmtPtr ast) {
    if (parser && ast) {
        parser->setAst(nodemap[ast]);
        nodemap.clear();
    }
}

void smt_reportError(SmtPrsr parser, unsigned int rowLeft, unsigned int colLeft,
                     unsigned int rowRight, unsigned int colRight, const char *msg) {
    if (parser && msg) {
        parser->reportError(rowLeft, colLeft, rowRight, colRight, msg);
    }
}

void smt_setLocation(SmtPrsr parser, SmtPtr ptr, int rowLeft, int colLeft, int rowRight, int colRight) {
    ptr->setFilename(parser->getFilename());
    ptr->setRowLeft(rowLeft);
    ptr->setColLeft(colLeft);
    ptr->setRowRight(rowRight);
    ptr->setColRight(colRight);
}

int smt_bool_value(SmtPtr ptr) {
    std::shared_ptr<BooleanValue> val = share<BooleanValue>(ptr);
    if (val) {
        return val->getValue();
    } else {
        return 2;
    }
}

// ast_attribute.h
SmtPtr smt_newAttribute1(SmtPtr keyword) {
    std::shared_ptr<Attribute> ptr = std::make_shared<Attribute>(share<Keyword>(keyword));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newAttribute2(SmtPtr keyword, SmtPtr attr_value) {
    std::shared_ptr<Attribute> ptr = std::make_shared<Attribute>(share<Keyword>(keyword),
                                                                 share<AttributeValue>(attr_value));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newCompoundAttributeValue(SmtList values) {
    std::shared_ptr<CompAttributeValue> ptr = std::make_shared<CompAttributeValue>(values->unwrap<AttributeValue>());
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_basic.h
SmtPtr smt_newSymbol(char const *value) {
    std::shared_ptr<Symbol> ptr = std::make_shared<Symbol>(value);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newKeyword(char const *value) {
    std::shared_ptr<Keyword> ptr = std::make_shared<Keyword>(value);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newMetaSpecConstant(int value) {
    std::shared_ptr<MetaSpecConstant> ptr = std::make_shared<MetaSpecConstant>(
            static_cast<MetaSpecConstant::Type>(value));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newBooleanValue(int value) {
    std::shared_ptr<BooleanValue> ptr = std::make_shared<BooleanValue>((bool) value);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newPropLiteral(SmtPtr symbol, int negated) {
    std::shared_ptr<PropLiteral> ptr = std::make_shared<PropLiteral>(share<Symbol>(symbol), (bool) negated);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_command.h
SmtPtr smt_newAssertCommand(SmtPtr term) {
    std::shared_ptr<AssertCommand> ptr = std::make_shared<AssertCommand>(share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newCheckSatCommand() {
    std::shared_ptr<CheckSatCommand> ptr = std::make_shared<CheckSatCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newCheckSatAssumCommand(SmtList assumptions) {
    std::vector<std::shared_ptr<PropLiteral>> v = assumptions->unwrap<PropLiteral>();
    std::shared_ptr<CheckSatAssumCommand> ptr = std::make_shared<CheckSatAssumCommand>(v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDeclareConstCommand(SmtPtr symbol, SmtPtr sort) {
    std::shared_ptr<DeclareConstCommand> ptr = std::make_shared<DeclareConstCommand>(share<Symbol>(symbol),
                                                                                     share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDeclareFunCommand(SmtPtr symbol, SmtList params, SmtPtr sort) {
    std::shared_ptr<DeclareFunCommand> ptr = std::make_shared<DeclareFunCommand>(share<Symbol>(symbol),
                                                                                 params->unwrap<Sort>(),
                                                                                 share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDeclareSortCommand(SmtPtr symbol, SmtPtr arity) {
    std::shared_ptr<DeclareSortCommand> ptr = std::make_shared<DeclareSortCommand>(share<Symbol>(symbol),
                                                                                   share<NumeralLiteral>(arity));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDefineFunCommand(SmtPtr definition) {
    std::shared_ptr<DefineFunCommand> ptr = std::make_shared<DefineFunCommand>(share<FunctionDefinition>(definition));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDefineFunRecCommand(SmtPtr definition) {
    std::shared_ptr<DefineFunRecCommand> ptr = std::make_shared<DefineFunRecCommand>(
            share<FunctionDefinition>(definition));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDefineFunsRecCommand(SmtList declarations, SmtList bodies) {
    std::vector<std::shared_ptr<FunctionDeclaration>> v1 = declarations->unwrap<FunctionDeclaration>();
    std::vector<std::shared_ptr<Term>> v2 = bodies->unwrap<Term>();
    std::shared_ptr<DefineFunsRecCommand> ptr = std::make_shared<DefineFunsRecCommand>(v1, v2);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDefineSortCommand(SmtPtr symbol, SmtList params, SmtPtr sort) {
    std::vector<std::shared_ptr<Symbol>> v1 = params->unwrap<Symbol>();
    std::shared_ptr<DefineSortCommand> ptr = std::make_shared<DefineSortCommand>(share<Symbol>(symbol), v1,
                                                                                 share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newEchoCommand(SmtPtr msg) {
    std::shared_ptr<EchoCommand> ptr = std::make_shared<EchoCommand>(share<StringLiteral>(msg)->getValue());
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newExitCommand() {
    std::shared_ptr<ExitCommand> ptr = std::make_shared<ExitCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetAssertsCommand() {
    std::shared_ptr<GetAssertsCommand> ptr = std::make_shared<GetAssertsCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetAssignsCommand() {
    std::shared_ptr<GetAssignsCommand> ptr = std::make_shared<GetAssignsCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetInfoCommand(SmtPtr keyword) {
    std::shared_ptr<GetInfoCommand> ptr = std::make_shared<GetInfoCommand>(share<Keyword>(keyword));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetModelCommand() {
    std::shared_ptr<GetModelCommand> ptr = std::make_shared<GetModelCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetOptionCommand(SmtPtr keyword) {
    std::shared_ptr<GetOptionCommand> ptr = std::make_shared<GetOptionCommand>(share<Keyword>(keyword));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetProofCommand() {
    std::shared_ptr<GetProofCommand> ptr = std::make_shared<GetProofCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetUnsatAssumsCommand() {
    std::shared_ptr<GetUnsatAssumsCommand> ptr = std::make_shared<GetUnsatAssumsCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetUnsatCoreCommand() {
    std::shared_ptr<GetUnsatCoreCommand> ptr = std::make_shared<GetUnsatCoreCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetValueCommand(SmtList terms) {
    std::vector<std::shared_ptr<Term>> v = terms->unwrap<Term>();
    std::shared_ptr<GetValueCommand> ptr = std::make_shared<GetValueCommand>(v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newPopCommand(SmtPtr numeral) {
    std::shared_ptr<PopCommand> ptr = std::make_shared<PopCommand>(share<NumeralLiteral>(numeral));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newPushCommand(SmtPtr numeral) {
    std::shared_ptr<PushCommand> ptr = std::make_shared<PushCommand>(share<NumeralLiteral>(numeral));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newResetCommand() {
    std::shared_ptr<ResetCommand> ptr = std::make_shared<ResetCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newResetAssertsCommand() {
    std::shared_ptr<ResetAssertsCommand> ptr = std::make_shared<ResetAssertsCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSetInfoCommand(SmtPtr info) {
    std::shared_ptr<SetInfoCommand> ptr = std::make_shared<SetInfoCommand>(share<Attribute>(info));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSetLogicCommand(SmtPtr logic) {
    std::shared_ptr<SetLogicCommand> ptr = std::make_shared<SetLogicCommand>(share<Symbol>(logic));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSetOptionCommand(SmtPtr option) {
    std::shared_ptr<SetOptionCommand> ptr = std::make_shared<SetOptionCommand>(share<Attribute>(option));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_fun.h
SmtPtr smt_newFunctionDeclaration(SmtPtr symbol, SmtList params, SmtPtr sort) {
    std::vector<std::shared_ptr<SortedVariable>> v = params->unwrap<SortedVariable>();
    std::shared_ptr<FunctionDeclaration> ptr = std::make_shared<FunctionDeclaration>(share<Symbol>(symbol), v,
                                                                                     share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newFunctionDefinition(SmtPtr signature, SmtPtr body) {
    std::shared_ptr<FunctionDefinition> ptr = std::make_shared<FunctionDefinition>(
            share<FunctionDeclaration>(signature), share<Term>(body));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_identifier.h
SmtPtr smt_newIdentifier1(SmtPtr symbol) {
    std::shared_ptr<Identifier> ptr = std::make_shared<Identifier>(share<Symbol>(symbol));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newIdentifier2(SmtPtr symbol, SmtList indices) {
    std::shared_ptr<Identifier> ptr = std::make_shared<Identifier>(share<Symbol>(symbol),
                                                                   indices->unwrap<Index>());
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newQualifiedIdentifier(SmtPtr identifier, SmtPtr sort) {
    std::shared_ptr<QualifiedIdentifier> ptr = std::make_shared<QualifiedIdentifier>(share<Identifier>(identifier),
                                                                                     share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_literal.h
SmtPtr smt_newNumeralLiteral(long value, unsigned int base) {
    std::shared_ptr<NumeralLiteral> ptr = std::make_shared<NumeralLiteral>(value, base);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDecimalLiteral(double value) {
    std::shared_ptr<DecimalLiteral> ptr = std::make_shared<DecimalLiteral>(value);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newStringLiteral(char const *value) {
    std::shared_ptr<StringLiteral> ptr = std::make_shared<StringLiteral>(value);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_logic.h
SmtPtr smt_newLogic(SmtPtr name, SmtList attributes) {
    std::vector<std::shared_ptr<Attribute>> v = attributes->unwrap<Attribute>();
    std::shared_ptr<Logic> ptr = std::make_shared<Logic>(share<Symbol>(name), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_s_expr.h
SmtPtr smt_newCompSExpression(SmtList exprs) {
    std::vector<std::shared_ptr<SExpression>> v = exprs->unwrap<SExpression>();
    std::shared_ptr<CompSExpression> ptr = std::make_shared<CompSExpression>(v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_script.h
SmtPtr smt_newSmtScript(SmtList cmds) {
    std::vector<std::shared_ptr<Command>> v = cmds->unwrap<Command>();
    std::shared_ptr<Script> ptr = std::make_shared<Script>(v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_sort.h
SmtPtr smt_newSort1(SmtPtr identifier) {
    std::shared_ptr<Sort> ptr = std::make_shared<Sort>(share<Identifier>(identifier));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSort2(SmtPtr identifier, SmtList params) {
    std::vector<std::shared_ptr<Sort>> v = params->unwrap<Sort>();
    std::shared_ptr<Sort> ptr = std::make_shared<Sort>(share<Identifier>(identifier), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_symbol_decl.h
SmtPtr smt_newSortSymbolDeclaration(SmtPtr identifier, SmtPtr arity, SmtList attributes) {
    std::vector<std::shared_ptr<Attribute>> v = attributes->unwrap<Attribute>();
    std::shared_ptr<SortSymbolDeclaration> ptr = std::make_shared<SortSymbolDeclaration>(share<Identifier>(identifier),
                                                                                         share<NumeralLiteral>(arity),
                                                                                         v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSpecConstFunDeclaration(SmtPtr constant, SmtPtr sort, SmtList attributes) {
    std::vector<std::shared_ptr<Attribute>> v = attributes->unwrap<Attribute>();
    std::shared_ptr<SpecConstFunDeclaration> ptr = std::make_shared<SpecConstFunDeclaration>(
            share<SpecConstant>(constant), share<Sort>(sort), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newMetaSpecConstFunDeclaration(SmtPtr constant, SmtPtr sort, SmtList attributes) {
    std::vector<std::shared_ptr<Attribute>> v = attributes->unwrap<Attribute>();
    std::shared_ptr<MetaSpecConstFunDeclaration> ptr = std::make_shared<MetaSpecConstFunDeclaration>(
            share<MetaSpecConstant>(constant), share<Sort>(sort), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newIdentifFunDeclaration(SmtPtr identifier, SmtList signature, SmtList attributes) {
    std::vector<std::shared_ptr<Sort>> v1 = signature->unwrap<Sort>();
    std::vector<std::shared_ptr<Attribute>> v2 = attributes->unwrap<Attribute>();
    std::shared_ptr<IdentifierFunDeclaration> ptr = std::make_shared<IdentifierFunDeclaration>(
            share<Identifier>(identifier), v1, v2);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newParamFunDeclaration(SmtList params, SmtPtr identifier, SmtList signature, SmtList attributes) {
    std::vector<std::shared_ptr<Symbol>> v1 = params->unwrap<Symbol>();
    std::vector<std::shared_ptr<Sort>> v2 = signature->unwrap<Sort>();
    std::vector<std::shared_ptr<Attribute>> v3 = attributes->unwrap<Attribute>();
    std::shared_ptr<ParametricFunDeclaration> ptr = std::make_shared<ParametricFunDeclaration>(v1, share<Identifier>(
            identifier), v2, v3);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_term.h
SmtPtr smt_newQualifiedTerm(SmtPtr identifier, SmtList terms) {
    std::vector<std::shared_ptr<Term>> v = terms->unwrap<Term>();
    std::shared_ptr<QualifiedTerm> ptr = std::make_shared<QualifiedTerm>(share<QIdentifier>(identifier), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newLetTerm(SmtList bindings, SmtPtr term) {
    std::vector<std::shared_ptr<VarBinding>> v = bindings->unwrap<VarBinding>();
    std::shared_ptr<LetTerm> ptr = std::make_shared<LetTerm>(v, share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newForallTerm(SmtList bindings, SmtPtr term) {
    std::vector<std::shared_ptr<SortedVariable>> v = bindings->unwrap<SortedVariable>();
    std::shared_ptr<ForallTerm> ptr = std::make_shared<ForallTerm>(v, share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newExistsTerm(SmtList bindings, SmtPtr term) {
    std::vector<std::shared_ptr<SortedVariable>> v = bindings->unwrap<SortedVariable>();
    std::shared_ptr<ExistsTerm> ptr = std::make_shared<ExistsTerm>(v, share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newAnnotatedTerm(SmtPtr term, SmtList attrs) {
    std::vector<std::shared_ptr<Attribute>> v = attrs->unwrap<Attribute>();
    std::shared_ptr<AnnotatedTerm> ptr = std::make_shared<AnnotatedTerm>(share<Term>(term), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_theory.h
SmtPtr smt_newTheory(SmtPtr name, SmtList attributes) {
    std::vector<std::shared_ptr<Attribute>> v = attributes->unwrap<Attribute>();
    std::shared_ptr<Theory> ptr =
            std::make_shared<Theory>(share<Symbol>(name), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_var.h
SmtPtr smt_newSortedVariable(SmtPtr symbol, SmtPtr sort) {
    std::shared_ptr<SortedVariable> ptr =
            std::make_shared<SortedVariable>(share<Symbol>(symbol), share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newVarBinding(SmtPtr symbol, SmtPtr term) {
    std::shared_ptr<VarBinding> ptr =
            std::make_shared<VarBinding>(share<Symbol>(symbol), share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}