cmake_minimum_required(VERSION 2.8.4)
project(parse-smtlib)

set(LIB_FLEX fl)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

include_directories("smtlib" "smtlib/ast" "smtlib/util" "smtlib/visitor" "smtlib/parser")
set(SOURCE_FILES
    main.cpp
	smtlib/ast/ast_abstract.h
	smtlib/ast/ast_attribute.h
	smtlib/ast/ast_attribute.cpp
	smtlib/ast/ast_basic.h
	smtlib/ast/ast_basic.cpp
	smtlib/ast/ast_classes.h
	smtlib/ast/ast_theory.h
	smtlib/ast/ast_theory.cpp
	smtlib/ast/ast_logic.cpp
	smtlib/ast/ast_logic.h
	smtlib/ast/ast_interfaces.h
	smtlib/ast/ast_script.cpp
	smtlib/ast/ast_script.h
	smtlib/ast/ast_command.cpp
	smtlib/ast/ast_command.h
	smtlib/ast/ast_symbol_decl.cpp
	smtlib/ast/ast_symbol_decl.h
	smtlib/ast/ast_sort.cpp
	smtlib/ast/ast_sort.h
	smtlib/ast/ast_literal.cpp
	smtlib/ast/ast_literal.h
	smtlib/ast/ast_sexp.cpp
	smtlib/ast/ast_sexp.h
	smtlib/ast/ast_identifier.cpp
	smtlib/ast/ast_identifier.h
	smtlib/ast/ast_fun.cpp
	smtlib/ast/ast_fun.h
	smtlib/ast/ast_var.cpp
	smtlib/ast/ast_var.h
	smtlib/ast/ast_term.cpp
	smtlib/ast/ast_term.h
	parser/smtlib-glue.h
	parser/smtlib-glue.cpp
	parser/smtlib-bison-parser.y.h
	parser/smtlib-bison-parser.y.c
	parser/smtlib-flex-lexer.l.c
	smtlib/parser/smt_parser.h
	smtlib/parser/smt_parser.cpp
	smtlib/util/logger.h
	smtlib/util/logger.cpp
	smtlib/visitor/ast_visitor.h
	smtlib/visitor/ast_visitor.cpp
	smtlib/visitor/ast_visitor_extra.h
	smtlib/visitor/ast_syntax_checker.h
	smtlib/visitor/ast_syntax_checker.cpp
	smtlib/parser/smt_symbol_table.h
	smtlib/parser/smt_symbol_table.cpp
	smtlib/parser/smt_symbol_stack.h
	smtlib/parser/smt_symbol_stack.cpp
	smtlib/parser/smt_symbol_util.h
    smtlib/parser/smt_symbol_util.cpp
	smtlib/visitor/ast_sortedness_checker.h
	smtlib/visitor/ast_sortedness_checker.cpp
	smtlib/visitor/ast_term_sorter.h
	smtlib/visitor/ast_term_sorter.cpp
	smtlib/ast/ast_datatype.h
	smtlib/ast/ast_datatype.cpp
	smtlib/ast/ast_match.h
	smtlib/ast/ast_match.cpp
	smtlib/util/global_settings.h
	smtlib/util/global_settings.cpp
	smtlib/smt_execution.h
	smtlib/smt_execution.cpp
	smtlib/smt_execution_settings.h
	smtlib/smt_execution_settings.cpp
	smtlib/util/error_messages.h
	smtlib/util/error_messages.cpp
	smtlib/visitor/ast_predicate_unfolder.h
	smtlib/visitor/ast_predicate_unfolder.cpp
	smtlib/visitor/ast_var_replacer.h
	smtlib/visitor/ast_var_replacer.cpp
	smtlib/visitor/ast_node_duplicator.h
	smtlib/visitor/ast_node_duplicator.cpp
)

add_executable(parse-smtlib ${SOURCE_FILES})
target_link_libraries(parse-smtlib ${LIB_FLEX})