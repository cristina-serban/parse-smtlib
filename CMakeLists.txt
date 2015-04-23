cmake_minimum_required(VERSION 2.8.4)
project(parse-smtlib)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
include_directories("smt" "smt/ast")

set(SOURCE_FILES
    main.cpp
	smt/ast/smt_abstract.h
	smt/ast/smt_attribute.h
	smt/ast/smt_attribute.cpp
	smt/ast/smt_basic.h
	smt/ast/smt_basic.cpp
	smt/ast/smt_theory.h
	smt/ast/smt_theory.cpp
	smt/ast/smt_logic.cpp
	smt/ast/smt_logic.h
	smt/ast/smt_interfaces.h
	smt/ast/smt_script.cpp
	smt/ast/smt_script.h
	smt/ast/smt_command.cpp
	smt/ast/smt_command.h
	smt/ast/smt_symbol_decl.cpp
	smt/ast/smt_symbol_decl.h
	smt/ast/smt_sort.cpp
	smt/ast/smt_sort.h
	smt/ast/smt_literal.cpp
	smt/ast/smt_literal.h
	smt/ast/smt_s_expr.cpp
	smt/ast/smt_s_expr.h
	smt/ast/smt_identifier.cpp
	smt/ast/smt_identifier.h
	smt/ast/smt_fun.cpp
	smt/ast/smt_fun.h
	smt/ast/smt_var.cpp
	smt/ast/smt_var.h
	smt/ast/smt_term.cpp
	smt/ast/smt_term.h
)

add_executable(parse-smtlib ${SOURCE_FILES})