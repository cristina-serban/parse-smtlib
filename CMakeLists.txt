cmake_minimum_required(VERSION 2.8.4)
project(parse-smtlib)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
include_directories("ast" "ast/smt")

set(SOURCE_FILES
    main.cpp
    ast/ast_node.h
    ast/smt/smt_abstract.h
    ast/smt/smt_attribute.h
    ast/smt/smt_attribute.cpp
    ast/smt/smt_basic.h
    ast/smt/smt_basic.cpp
    ast/smt/smt_theory.h
    ast/smt/smt_theory.cpp
)

add_executable(parse-smtlib ${SOURCE_FILES} ast/smt/smt_logic.cpp ast/smt/smt_logic.h ast/smt/smt_interfaces.h ast/smt/smt_script.cpp ast/smt/smt_script.h ast/smt/smt_command.cpp ast/smt/smt_command.h ast/smt/smt_symbol_decl.cpp ast/smt/smt_symbol_decl.h ast/smt/smt_sort.cpp ast/smt/smt_sort.h ast/smt/smt_literal.cpp ast/smt/smt_literal.h ast/smt/smt_s_expr.cpp ast/smt/smt_s_expr.h ast/smt/smt_identifier.cpp ast/smt/smt_identifier.h ast/smt/smt_fun.cpp ast/smt/smt_fun.h ast/smt/smt_var.cpp ast/smt/smt_var.h ast/smt/smt_term.cpp ast/smt/smt_term.h)