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

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

unordered_map<smtlib::ast::AstNode*, shared_ptr<smtlib::ast::AstNode>> nodemap;

template<class T>
shared_ptr<T> share(SmtPtr nakedPtr) {
    return dynamic_pointer_cast<T>(nodemap[nakedPtr]);
}

template<>
shared_ptr<SpecConstant> share(SmtPtr nakedPtr) {
    shared_ptr<NumeralLiteral> option1 = dynamic_pointer_cast<NumeralLiteral>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    shared_ptr<DecimalLiteral> option2 = dynamic_pointer_cast<DecimalLiteral>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    shared_ptr<StringLiteral> option3 = dynamic_pointer_cast<StringLiteral>(nodemap[nakedPtr]);
    if (option3) {
        return option3->shared_from_this();
    }

    throw;
}

template<>
shared_ptr<Command> share(SmtPtr nakedPtr) {
    shared_ptr<AssertCommand> option1 = dynamic_pointer_cast<AssertCommand>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    shared_ptr<CheckSatCommand> option2 = dynamic_pointer_cast<CheckSatCommand>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    shared_ptr<CheckSatAssumCommand> option3 = dynamic_pointer_cast<CheckSatAssumCommand>(nodemap[nakedPtr]);
    if (option3) {
        return option3->shared_from_this();
    }

    shared_ptr<DeclareConstCommand> option4 = dynamic_pointer_cast<DeclareConstCommand>(nodemap[nakedPtr]);
    if (option4) {
        return option4->shared_from_this();
    }

    shared_ptr<DeclareFunCommand> option5 = dynamic_pointer_cast<DeclareFunCommand>(nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    shared_ptr<DeclareSortCommand> option6 = dynamic_pointer_cast<DeclareSortCommand>(nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    shared_ptr<DefineFunCommand> option7 = dynamic_pointer_cast<DefineFunCommand>(nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    shared_ptr<DefineFunRecCommand> option8 = dynamic_pointer_cast<DefineFunRecCommand>(nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    shared_ptr<DefineFunsRecCommand> option9 = dynamic_pointer_cast<DefineFunsRecCommand>(nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    shared_ptr<DefineSortCommand> option10 = dynamic_pointer_cast<DefineSortCommand>(nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    shared_ptr<EchoCommand> option11 = dynamic_pointer_cast<EchoCommand>(nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    shared_ptr<ExitCommand> option12 = dynamic_pointer_cast<ExitCommand>(nodemap[nakedPtr]);
    if (option12) {
        return option12->shared_from_this();
    }

    shared_ptr<SetOptionCommand> option13 = dynamic_pointer_cast<SetOptionCommand>(nodemap[nakedPtr]);
    if (option13) {
        return option13->shared_from_this();
    }

    shared_ptr<GetAssertsCommand> option14 = dynamic_pointer_cast<GetAssertsCommand>(nodemap[nakedPtr]);
    if (option14) {
        return option14->shared_from_this();
    }

    shared_ptr<GetAssignsCommand> option15 = dynamic_pointer_cast<GetAssignsCommand>(nodemap[nakedPtr]);
    if (option15) {
        return option15->shared_from_this();
    }

    shared_ptr<GetInfoCommand> option16 = dynamic_pointer_cast<GetInfoCommand>(nodemap[nakedPtr]);
    if (option16) {
        return option16->shared_from_this();
    }

    shared_ptr<GetModelCommand> option17 = dynamic_pointer_cast<GetModelCommand>(nodemap[nakedPtr]);
    if (option17) {
        return option17->shared_from_this();
    }

    shared_ptr<GetOptionCommand> option18 = dynamic_pointer_cast<GetOptionCommand>(nodemap[nakedPtr]);
    if (option18) {
        return option18->shared_from_this();
    }

    shared_ptr<GetProofCommand> option19 = dynamic_pointer_cast<GetProofCommand>(nodemap[nakedPtr]);
    if (option19) {
        return option19->shared_from_this();
    }

    shared_ptr<GetUnsatAssumsCommand> option20 = dynamic_pointer_cast<GetUnsatAssumsCommand>(nodemap[nakedPtr]);
    if (option20) {
        return option20->shared_from_this();
    }

    shared_ptr<GetUnsatCoreCommand> option21 = dynamic_pointer_cast<GetUnsatCoreCommand>(nodemap[nakedPtr]);
    if (option21) {
        return option21->shared_from_this();
    }

    shared_ptr<GetValueCommand> option22 = dynamic_pointer_cast<GetValueCommand>(nodemap[nakedPtr]);
    if (option22) {
        return option22->shared_from_this();
    }

    shared_ptr<PopCommand> option23 = dynamic_pointer_cast<PopCommand>(nodemap[nakedPtr]);
    if (option23) {
        return option23->shared_from_this();
    }

    shared_ptr<PushCommand> option24 = dynamic_pointer_cast<PushCommand>(nodemap[nakedPtr]);
    if (option24) {
        return option24->shared_from_this();
    }

    shared_ptr<ResetCommand> option25 = dynamic_pointer_cast<ResetCommand>(nodemap[nakedPtr]);
    if (option25) {
        return option25->shared_from_this();
    }

    shared_ptr<ResetAssertsCommand> option26 = dynamic_pointer_cast<ResetAssertsCommand>(nodemap[nakedPtr]);
    if (option26) {
        return option26->shared_from_this();
    }

    shared_ptr<SetInfoCommand> option27 = dynamic_pointer_cast<SetInfoCommand>(nodemap[nakedPtr]);
    if (option27) {
        return option27->shared_from_this();
    }

    shared_ptr<SetLogicCommand> option28 = dynamic_pointer_cast<SetLogicCommand>(nodemap[nakedPtr]);
    if (option28) {
        return option28->shared_from_this();
    }

    shared_ptr<DeclareDatatypeCommand> option29 = dynamic_pointer_cast<DeclareDatatypeCommand>(nodemap[nakedPtr]);
    if (option29) {
        return option29->shared_from_this();
    }

    shared_ptr<DeclareDatatypesCommand> option30 = dynamic_pointer_cast<DeclareDatatypesCommand>(nodemap[nakedPtr]);
    if (option30) {
        return option30->shared_from_this();
    }

    throw;
}

template<>
shared_ptr<FunSymbolDeclaration> share(SmtPtr nakedPtr) {
    shared_ptr<SpecConstFunDeclaration> option6 = dynamic_pointer_cast<SpecConstFunDeclaration>(nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    shared_ptr<MetaSpecConstFunDeclaration> option7 = dynamic_pointer_cast<MetaSpecConstFunDeclaration>(
            nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    shared_ptr<SimpleFunDeclaration> option8 = dynamic_pointer_cast<SimpleFunDeclaration>(nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    shared_ptr<ParametricFunDeclaration> option9 = dynamic_pointer_cast<ParametricFunDeclaration>(nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    throw;
}

template<>
shared_ptr<Constructor> share(SmtPtr nakedPtr) {
    shared_ptr<Symbol> option1 = dynamic_pointer_cast<Symbol>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    shared_ptr<QualifiedConstructor> option2 = dynamic_pointer_cast<QualifiedConstructor>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
shared_ptr<Pattern> share(SmtPtr nakedPtr) {
    if (dynamic_cast<Constructor*>(nakedPtr)) {
        return share<Constructor>(nakedPtr);
    }

    shared_ptr<Symbol> option1 = dynamic_pointer_cast<Symbol>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    shared_ptr<QualifiedPattern> option2 = dynamic_pointer_cast<QualifiedPattern>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
shared_ptr<DatatypeDeclaration> share(SmtPtr nakedPtr) {
    shared_ptr<SimpleDatatypeDeclaration> option1 =
            dynamic_pointer_cast<SimpleDatatypeDeclaration>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    shared_ptr<ParametricDatatypeDeclaration> option2 =
            dynamic_pointer_cast<ParametricDatatypeDeclaration>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
shared_ptr<AttributeValue> share(SmtPtr nakedPtr) {
    shared_ptr<BooleanValue> option1 = dynamic_pointer_cast<BooleanValue>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    shared_ptr<SortSymbolDeclaration> option5 = dynamic_pointer_cast<SortSymbolDeclaration>(nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    if (dynamic_cast<FunSymbolDeclaration*>(nakedPtr)) {
        return share<FunSymbolDeclaration>(nakedPtr);
    }

    shared_ptr<Symbol> option10 = dynamic_pointer_cast<Symbol>(nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    shared_ptr<CompSExpression> option11 = dynamic_pointer_cast<CompSExpression>(nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    shared_ptr<CompAttributeValue> option12 = dynamic_pointer_cast<CompAttributeValue>(nodemap[nakedPtr]);
    if (option12) {
        return option12->shared_from_this();
    }

    throw;
}

template<>
shared_ptr<SExpression> share(SmtPtr nakedPtr) {
    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    shared_ptr<Symbol> option4 = dynamic_pointer_cast<Symbol>(nodemap[nakedPtr]);
    if (option4) {
        return option4->shared_from_this();
    }

    shared_ptr<Keyword> option5 = dynamic_pointer_cast<Keyword>(nodemap[nakedPtr]);
    if (option5) {
        return option5->shared_from_this();
    }

    shared_ptr<CompSExpression> option6 = dynamic_pointer_cast<CompSExpression>(nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    throw;
}

template<>
shared_ptr<Identifier> share(SmtPtr nakedPtr) {
    shared_ptr<SimpleIdentifier> option1 = dynamic_pointer_cast<SimpleIdentifier>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    shared_ptr<QualifiedIdentifier> option2 = dynamic_pointer_cast<QualifiedIdentifier>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

template<>
shared_ptr<Term> share(SmtPtr nakedPtr) {
    if (dynamic_cast<SpecConstant*>(nakedPtr)) {
        return share<SpecConstant>(nakedPtr);
    }

    if (dynamic_cast<Identifier*>(nakedPtr)) {
        return share<Identifier>(nakedPtr);
    }

    shared_ptr<AnnotatedTerm> option6 = dynamic_pointer_cast<AnnotatedTerm>(nodemap[nakedPtr]);
    if (option6) {
        return option6->shared_from_this();
    }

    shared_ptr<ExistsTerm> option7 = dynamic_pointer_cast<ExistsTerm>(nodemap[nakedPtr]);
    if (option7) {
        return option7->shared_from_this();
    }

    shared_ptr<ForallTerm> option8 = dynamic_pointer_cast<ForallTerm>(nodemap[nakedPtr]);
    if (option8) {
        return option8->shared_from_this();
    }

    shared_ptr<LetTerm> option9 = dynamic_pointer_cast<LetTerm>(nodemap[nakedPtr]);
    if (option9) {
        return option9->shared_from_this();
    }

    shared_ptr<QualifiedTerm> option10 = dynamic_pointer_cast<QualifiedTerm>(nodemap[nakedPtr]);
    if (option10) {
        return option10->shared_from_this();
    }

    shared_ptr<MatchTerm> option11 = dynamic_pointer_cast<MatchTerm>(nodemap[nakedPtr]);
    if (option11) {
        return option11->shared_from_this();
    }

    throw;
}

template<>
shared_ptr<Index> share(SmtPtr nakedPtr) {
    shared_ptr<NumeralLiteral> option1 = dynamic_pointer_cast<NumeralLiteral>(nodemap[nakedPtr]);
    if (option1) {
        return option1->shared_from_this();
    }

    shared_ptr<Symbol> option2 = dynamic_pointer_cast<Symbol>(nodemap[nakedPtr]);
    if (option2) {
        return option2->shared_from_this();
    }

    throw;
}

//namespace smtlib {
//namespace ast {

class ParserInternalList {
private:
    vector<SmtPtr> v;
public:
    template<class T>
    vector<shared_ptr<T>> unwrap() {
        vector<shared_ptr<T>> result;
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
    cout << ptr->toString();
}

void smt_setAst(SmtPrsr parser, SmtPtr ast) {
    if (parser && ast) {
        parser->setAst(nodemap[ast]);
        nodemap.clear();
    }
}

void smt_reportError(SmtPrsr parser, unsigned int rowLeft, unsigned int colLeft,
                     unsigned int rowRight, unsigned int colRight, const char* msg) {
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
    shared_ptr<BooleanValue> val = share<BooleanValue>(ptr);
    if (val) {
        return val->getValue();
    } else {
        return 2;
    }
}

// ast_attribute.h
SmtPtr smt_newAttribute1(SmtPtr keyword) {
    shared_ptr<Attribute> ptr = make_shared<Attribute>(share<Keyword>(keyword));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newAttribute2(SmtPtr keyword, SmtPtr attr_value) {
    shared_ptr<Attribute> ptr = make_shared<Attribute>(share<Keyword>(keyword),
                                                       share<AttributeValue>(attr_value));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newCompAttributeValue(SmtList values) {
    vector<shared_ptr<AttributeValue>> v = values->unwrap<AttributeValue>();
    shared_ptr<CompAttributeValue> ptr = make_shared<CompAttributeValue>(v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_basic.h
SmtPtr smt_newSymbol(char const* value) {
    shared_ptr<Symbol> ptr = make_shared<Symbol>(value);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newKeyword(char const* value) {
    shared_ptr<Keyword> ptr = make_shared<Keyword>(value);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newMetaSpecConstant(int value) {
    shared_ptr<MetaSpecConstant> ptr = make_shared<MetaSpecConstant>(
            static_cast<MetaSpecConstant::Type>(value));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newBooleanValue(int value) {
    shared_ptr<BooleanValue> ptr = make_shared<BooleanValue>((bool) value);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newPropLiteral(SmtPtr symbol, int negated) {
    shared_ptr<PropLiteral> ptr = make_shared<PropLiteral>(share<Symbol>(symbol), (bool) negated);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_command.h
SmtPtr smt_newAssertCommand(SmtPtr term) {
    shared_ptr<AssertCommand> ptr = make_shared<AssertCommand>(share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newCheckSatCommand() {
    shared_ptr<CheckSatCommand> ptr = make_shared<CheckSatCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newCheckSatAssumCommand(SmtList assumptions) {
    vector<shared_ptr<PropLiteral>> v = assumptions->unwrap<PropLiteral>();
    shared_ptr<CheckSatAssumCommand> ptr = make_shared<CheckSatAssumCommand>(v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDeclareConstCommand(SmtPtr symbol, SmtPtr sort) {
    shared_ptr<DeclareConstCommand> ptr =
            make_shared<DeclareConstCommand>(share<Symbol>(symbol), share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDeclareDatatypeCommand(SmtPtr symbol, SmtPtr declaration) {
    shared_ptr<DeclareDatatypeCommand> ptr =
            make_shared<DeclareDatatypeCommand>(share<Symbol>(symbol),
                                                share<DatatypeDeclaration>(declaration));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDeclareDatatypesCommand(SmtList sorts, SmtList declarations) {
    vector<shared_ptr<SortDeclaration>> v1 = sorts->unwrap<SortDeclaration>();
    vector<shared_ptr<DatatypeDeclaration>> v2 = declarations->unwrap<DatatypeDeclaration>();
    shared_ptr<DeclareDatatypesCommand> ptr = make_shared<DeclareDatatypesCommand>(v1, v2);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDeclareFunCommand(SmtPtr symbol, SmtList params, SmtPtr sort) {
    vector<shared_ptr<Sort>> v = params->unwrap<Sort>();
    shared_ptr<DeclareFunCommand> ptr =
            make_shared<DeclareFunCommand>(share<Symbol>(symbol), v, share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDeclareSortCommand(SmtPtr symbol, SmtPtr arity) {
    shared_ptr<DeclareSortCommand> ptr =
            make_shared<DeclareSortCommand>(share<Symbol>(symbol), share<NumeralLiteral>(arity));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDefineFunCommand(SmtPtr definition) {
    shared_ptr<DefineFunCommand> ptr =
            make_shared<DefineFunCommand>(share<FunctionDefinition>(definition));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDefineFunRecCommand(SmtPtr definition) {
    shared_ptr<DefineFunRecCommand> ptr = make_shared<DefineFunRecCommand>(
            share<FunctionDefinition>(definition));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDefineFunsRecCommand(SmtList declarations, SmtList bodies) {
    vector<shared_ptr<FunctionDeclaration>> v1 = declarations->unwrap<FunctionDeclaration>();
    vector<shared_ptr<Term>> v2 = bodies->unwrap<Term>();
    shared_ptr<DefineFunsRecCommand> ptr = make_shared<DefineFunsRecCommand>(v1, v2);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDefineSortCommand(SmtPtr symbol, SmtList params, SmtPtr sort) {
    vector<shared_ptr<Symbol>> v1 = params->unwrap<Symbol>();
    shared_ptr<DefineSortCommand> ptr =
            make_shared<DefineSortCommand>(share<Symbol>(symbol), v1, share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newEchoCommand(SmtPtr msg) {
    shared_ptr<EchoCommand> ptr = make_shared<EchoCommand>(share<StringLiteral>(msg)->getValue());
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newExitCommand() {
    shared_ptr<ExitCommand> ptr = make_shared<ExitCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetAssertsCommand() {
    shared_ptr<GetAssertsCommand> ptr = make_shared<GetAssertsCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetAssignsCommand() {
    shared_ptr<GetAssignsCommand> ptr = make_shared<GetAssignsCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetInfoCommand(SmtPtr keyword) {
    shared_ptr<GetInfoCommand> ptr = make_shared<GetInfoCommand>(share<Keyword>(keyword));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetModelCommand() {
    shared_ptr<GetModelCommand> ptr = make_shared<GetModelCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetOptionCommand(SmtPtr keyword) {
    shared_ptr<GetOptionCommand> ptr = make_shared<GetOptionCommand>(share<Keyword>(keyword));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetProofCommand() {
    shared_ptr<GetProofCommand> ptr = make_shared<GetProofCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetUnsatAssumsCommand() {
    shared_ptr<GetUnsatAssumsCommand> ptr = make_shared<GetUnsatAssumsCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetUnsatCoreCommand() {
    shared_ptr<GetUnsatCoreCommand> ptr = make_shared<GetUnsatCoreCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newGetValueCommand(SmtList terms) {
    vector<shared_ptr<Term>> v = terms->unwrap<Term>();
    shared_ptr<GetValueCommand> ptr = make_shared<GetValueCommand>(v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newPopCommand(SmtPtr numeral) {
    shared_ptr<PopCommand> ptr = make_shared<PopCommand>(share<NumeralLiteral>(numeral));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newPushCommand(SmtPtr numeral) {
    shared_ptr<PushCommand> ptr = make_shared<PushCommand>(share<NumeralLiteral>(numeral));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newResetCommand() {
    shared_ptr<ResetCommand> ptr = make_shared<ResetCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newResetAssertsCommand() {
    shared_ptr<ResetAssertsCommand> ptr = make_shared<ResetAssertsCommand>();
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSetInfoCommand(SmtPtr info) {
    shared_ptr<SetInfoCommand> ptr = make_shared<SetInfoCommand>(share<Attribute>(info));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSetLogicCommand(SmtPtr logic) {
    shared_ptr<SetLogicCommand> ptr = make_shared<SetLogicCommand>(share<Symbol>(logic));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSetOptionCommand(SmtPtr option) {
    shared_ptr<SetOptionCommand> ptr = make_shared<SetOptionCommand>(share<Attribute>(option));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

//smt_datatype.h
SmtPtr smt_newSortDeclaration(SmtPtr symbol, SmtPtr numeral) {
    shared_ptr<SortDeclaration> ptr =
            make_shared<SortDeclaration>(share<Symbol>(symbol), share<NumeralLiteral>(numeral));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSelectorDeclaration(SmtPtr symbol, SmtPtr sort) {
    shared_ptr<SelectorDeclaration> ptr =
            make_shared<SelectorDeclaration>(share<Symbol>(symbol), share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newConstructorDeclaration(SmtPtr symbol, SmtList selectors) {
    vector<shared_ptr<SelectorDeclaration>> v = selectors->unwrap<SelectorDeclaration>();
    shared_ptr<ConstructorDeclaration> ptr = make_shared<ConstructorDeclaration>(share<Symbol>(symbol), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSimpleDatatypeDeclaration(SmtList constructors) {
    vector<shared_ptr<ConstructorDeclaration>> v = constructors->unwrap<ConstructorDeclaration>();
    shared_ptr<SimpleDatatypeDeclaration> ptr = make_shared<SimpleDatatypeDeclaration>(v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newParametricDatatypeDeclaration(SmtList params, SmtList constructors) {
    vector<shared_ptr<Symbol>> v1 = constructors->unwrap<Symbol>();
    vector<shared_ptr<ConstructorDeclaration>> v2 = constructors->unwrap<ConstructorDeclaration>();
    shared_ptr<ParametricDatatypeDeclaration> ptr = make_shared<ParametricDatatypeDeclaration>(v1, v2);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_fun.h
SmtPtr smt_newFunctionDeclaration(SmtPtr symbol, SmtList params, SmtPtr sort) {
    vector<shared_ptr<SortedVariable>> v = params->unwrap<SortedVariable>();
    shared_ptr<FunctionDeclaration> ptr =
            make_shared<FunctionDeclaration>(share<Symbol>(symbol), v, share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newFunctionDefinition(SmtPtr signature, SmtPtr body) {
    shared_ptr<FunctionDefinition> ptr = make_shared<FunctionDefinition>(
            share<FunctionDeclaration>(signature), share<Term>(body));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_identifier.h
SmtPtr smt_newSimpleIdentifier1(SmtPtr symbol) {
    shared_ptr<SimpleIdentifier> ptr = make_shared<SimpleIdentifier>(share<Symbol>(symbol));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSimpleIdentifier2(SmtPtr symbol, SmtList indices) {
    vector<shared_ptr<Index>> v = indices->unwrap<Index>();
    shared_ptr<SimpleIdentifier> ptr =
            make_shared<SimpleIdentifier>(share<Symbol>(symbol), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newQualifiedIdentifier(SmtPtr identifier, SmtPtr sort) {
    shared_ptr<QualifiedIdentifier> ptr =
            make_shared<QualifiedIdentifier>(share<SimpleIdentifier>(identifier), share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_literal.h
SmtPtr smt_newNumeralLiteral(long value, unsigned int base) {
    shared_ptr<NumeralLiteral> ptr = make_shared<NumeralLiteral>(value, base);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newDecimalLiteral(double value) {
    shared_ptr<DecimalLiteral> ptr = make_shared<DecimalLiteral>(value);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newStringLiteral(char const* value) {
    shared_ptr<StringLiteral> ptr = make_shared<StringLiteral>(value);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_logic.h
SmtPtr smt_newLogic(SmtPtr name, SmtList attributes) {
    vector<shared_ptr<Attribute>> v = attributes->unwrap<Attribute>();
    shared_ptr<Logic> ptr = make_shared<Logic>(share<Symbol>(name), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_match.h
SmtPtr smt_newQualifiedConstructor(SmtPtr symbol, SmtPtr sort) {
    shared_ptr<QualifiedConstructor> ptr =
            make_shared<QualifiedConstructor>(share<Symbol>(symbol), share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newQualifiedPattern(SmtPtr constructor, SmtList symbols) {
    vector<shared_ptr<Symbol>> v = symbols->unwrap<Symbol>();
    shared_ptr<QualifiedPattern> ptr = make_shared<QualifiedPattern>(share<Constructor>(constructor), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newMatchCase(SmtPtr pattern, SmtPtr term) {
    shared_ptr<MatchCase> ptr =
            make_shared<MatchCase>(share<Pattern>(pattern), share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_s_exp.h
SmtPtr smt_newCompSExpression(SmtList exprs) {
    vector<shared_ptr<SExpression>> v = exprs->unwrap<SExpression>();
    shared_ptr<CompSExpression> ptr = make_shared<CompSExpression>(v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_script.h
SmtPtr smt_newSmtScript(SmtList cmds) {
    vector<shared_ptr<Command>> v = cmds->unwrap<Command>();
    shared_ptr<Script> ptr = make_shared<Script>(v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_sort.h
SmtPtr smt_newSort1(SmtPtr identifier) {
    shared_ptr<Sort> ptr = make_shared<Sort>(share<SimpleIdentifier>(identifier));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSort2(SmtPtr identifier, SmtList params) {
    vector<shared_ptr<Sort>> v = params->unwrap<Sort>();
    shared_ptr<Sort> ptr = make_shared<Sort>(share<SimpleIdentifier>(identifier), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_symbol_decl.h
SmtPtr smt_newSortSymbolDeclaration(SmtPtr identifier, SmtPtr arity, SmtList attributes) {
    vector<shared_ptr<Attribute>> v = attributes->unwrap<Attribute>();
    shared_ptr<SortSymbolDeclaration> ptr =
            make_shared<SortSymbolDeclaration>(share<SimpleIdentifier>(identifier),
                                               share<NumeralLiteral>(arity), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSpecConstFunDeclaration(SmtPtr constant, SmtPtr sort, SmtList attributes) {
    vector<shared_ptr<Attribute>> v = attributes->unwrap<Attribute>();
    shared_ptr<SpecConstFunDeclaration> ptr =
            make_shared<SpecConstFunDeclaration>(share<SpecConstant>(constant), share<Sort>(sort), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newMetaSpecConstFunDeclaration(SmtPtr constant, SmtPtr sort, SmtList attributes) {
    vector<shared_ptr<Attribute>> v = attributes->unwrap<Attribute>();
    shared_ptr<MetaSpecConstFunDeclaration> ptr =
            make_shared<MetaSpecConstFunDeclaration>(share<MetaSpecConstant>(constant), share<Sort>(sort), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newSimpleFunDeclaration(SmtPtr identifier, SmtList signature, SmtList attributes) {
    vector<shared_ptr<Sort>> v1 = signature->unwrap<Sort>();
    vector<shared_ptr<Attribute>> v2 = attributes->unwrap<Attribute>();
    shared_ptr<SimpleFunDeclaration> ptr =
            make_shared<SimpleFunDeclaration>(share<SimpleIdentifier>(identifier), v1, v2);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newParametricFunDeclaration(SmtList params, SmtPtr identifier, SmtList signature, SmtList attributes) {
    vector<shared_ptr<Symbol>> v1 = params->unwrap<Symbol>();
    vector<shared_ptr<Sort>> v2 = signature->unwrap<Sort>();
    vector<shared_ptr<Attribute>> v3 = attributes->unwrap<Attribute>();
    shared_ptr<ParametricFunDeclaration> ptr =
            make_shared<ParametricFunDeclaration>(v1, share<SimpleIdentifier>(identifier), v2, v3);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_term.h
SmtPtr smt_newQualifiedTerm(SmtPtr identifier, SmtList terms) {
    vector<shared_ptr<Term>> v = terms->unwrap<Term>();
    shared_ptr<QualifiedTerm> ptr = make_shared<QualifiedTerm>(share<Identifier>(identifier), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newLetTerm(SmtList bindings, SmtPtr term) {
    vector<shared_ptr<VarBinding>> v = bindings->unwrap<VarBinding>();
    shared_ptr<LetTerm> ptr = make_shared<LetTerm>(v, share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newForallTerm(SmtList bindings, SmtPtr term) {
    vector<shared_ptr<SortedVariable>> v = bindings->unwrap<SortedVariable>();
    shared_ptr<ForallTerm> ptr = make_shared<ForallTerm>(v, share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newExistsTerm(SmtList bindings, SmtPtr term) {
    vector<shared_ptr<SortedVariable>> v = bindings->unwrap<SortedVariable>();
    shared_ptr<ExistsTerm> ptr = make_shared<ExistsTerm>(v, share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newMatchTerm(SmtPtr term, SmtList cases) {
    vector<shared_ptr<MatchCase>> v = cases->unwrap<MatchCase>();
    shared_ptr<MatchTerm> ptr = make_shared<MatchTerm>(share<Term>(term), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newAnnotatedTerm(SmtPtr term, SmtList attrs) {
    vector<shared_ptr<Attribute>> v = attrs->unwrap<Attribute>();
    shared_ptr<AnnotatedTerm> ptr = make_shared<AnnotatedTerm>(share<Term>(term), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_theory.h
SmtPtr smt_newTheory(SmtPtr name, SmtList attributes) {
    vector<shared_ptr<Attribute>> v = attributes->unwrap<Attribute>();
    shared_ptr<Theory> ptr =
            make_shared<Theory>(share<Symbol>(name), v);
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

// smt_var.h
SmtPtr smt_newSortedVariable(SmtPtr symbol, SmtPtr sort) {
    shared_ptr<SortedVariable> ptr =
            make_shared<SortedVariable>(share<Symbol>(symbol), share<Sort>(sort));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}

SmtPtr smt_newVarBinding(SmtPtr symbol, SmtPtr term) {
    shared_ptr<VarBinding> ptr =
            make_shared<VarBinding>(share<Symbol>(symbol), share<Term>(term));
    nodemap[ptr.get()] = ptr;
    return ptr.get();
}