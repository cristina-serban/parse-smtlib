smtlib-parser:
	bison -d smtlib-bison-parser.y -Wconflicts-sr
	mv smtlib-bison-parser.tab.h smtlib-bison-parser.y.h
	mv smtlib-bison-parser.tab.c smtlib-bison-parser.y.c
	flex smtlib-flex-lexer.l
	mv lex.yy.c smtlib-flex-lexer.l.c
	g++ -g -c smtlib-flex-lexer.l.c -o smtlib-flex-lexer.l.o
	g++ -g -c smtlib-bison-parser.y.c -o smtlib-bison-parser.y.o
	g++ -g -c -std=c++11 smtlib-glue.cpp -o smtlib-glue.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_attribute.cpp -o ast_attribute.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_basic.cpp -o ast_basic.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_command.cpp -o ast_command.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_fun.cpp -o ast_fun.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_identifier.cpp -o ast_identifier.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_literal.cpp -o ast_literal.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_logic.cpp -o ast_logic.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_sexp.cpp -o ast_sexp.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_script.cpp -o ast_script.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_sort.cpp -o ast_sort.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_symbol_decl.cpp -o ast_symbol_decl.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_term.cpp -o ast_term.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_theory.cpp -o ast_theory.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_var.cpp -o ast_var.o
	g++ -g -c -std=c++11 ../smtlib/parser/smt_parser.cpp -o smt_parser.o
	g++ -g -c -std=c++11 ../smtlib/util/smt_logger.cpp -o smt_logger.o
	g++ -g -o parse-smtlib smtlib-flex-lexer.l.o smtlib-bison-parser.y.o smtlib-glue.o ast_attribute.o ast_basic.o ast_command.o ast_fun.o ast_identifier.o ast_literal.o ast_logic.o ast_sexp.o ast_sort.o ast_script.o ast_symbol_decl.o ast_term.o ast_theory.o ast_var.o smt_parser.o smt_logger.o -lfl
	rm -f *.o
clean:
	rm -f smtlib-bison-parser.y.h
	rm -f smtlib-bison-parser.y.c
	rm -f smtlib-flex-lexer.l.c
	rm -f *.o
	rm -f parse-smtlib
