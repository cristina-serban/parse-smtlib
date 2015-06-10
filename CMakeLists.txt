cmake_minimum_required(VERSION 2.8.4)
project(parse-smtlib)

set(LIB_FLEX fl)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
include_directories("smtlib" "smtlib/ast")

set(SOURCE_FILES
    main.cpp
	smtlib/ast/smt_abstract.h
	smtlib/ast/smt_attribute.h
	smtlib/ast/smt_attribute.cpp
	smtlib/ast/smt_basic.h
	smtlib/ast/smt_basic.cpp
	smtlib/ast/smt_theory.h
	smtlib/ast/smt_theory.cpp
	smtlib/ast/smt_logic.cpp
	smtlib/ast/smt_logic.h
	smtlib/ast/smt_interfaces.h
	smtlib/ast/smt_script.cpp
	smtlib/ast/smt_script.h
	smtlib/ast/smt_command.cpp
	smtlib/ast/smt_command.h
	smtlib/ast/smt_symbol_decl.cpp
	smtlib/ast/smt_symbol_decl.h
	smtlib/ast/smt_sort.cpp
	smtlib/ast/smt_sort.h
	smtlib/ast/smt_literal.cpp
	smtlib/ast/smt_literal.h
	smtlib/ast/smt_s_expr.cpp
	smtlib/ast/smt_s_expr.h
	smtlib/ast/smt_identifier.cpp
	smtlib/ast/smt_identifier.h
	smtlib/ast/smt_fun.cpp
	smtlib/ast/smt_fun.h
	smtlib/ast/smt_var.cpp
	smtlib/ast/smt_var.h
	smtlib/ast/smt_term.cpp
	smtlib/ast/smt_term.h
	parser/smtlib-glue.h
	parser/smtlib-glue.cpp
	parser/smtlib-bison-parser.y.h
	parser/smtlib-bison-parser.y.c
	parser/smtlib-flex-lexer.l.c
	smtlib/parser/smt_parser.h
	smtlib/parser/smt_parser.cpp
)

add_executable(parse-smtlib ${SOURCE_FILES} smtlib/util/smt_logger.h smtlib/util/smt_logger.cpp smtlib/visitor/ast_visitor.h smtlib/visitor/ast_visitor.cpp smtlib/ast/smt_classes.h)
target_link_libraries(parse-smtlib ${LIB_FLEX})