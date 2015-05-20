smtlib-parser:
	bison -d smtlib-bison-parser.y -Wconflicts-sr
	mv smtlib-bison-parser.tab.h smtlib-bison-parser.y.h
	mv smtlib-bison-parser.tab.c smtlib-bison-parser.y.c
	flex smtlib-flex-lexer.l
	mv lex.yy.c smtlib-flex-lexer.l.c
	g++ -g -c smtlib-flex-lexer.l.c -o smtlib-flex-lexer.l.o
	g++ -g -c smtlib-bison-parser.y.c -o smtlib-bison-parser.y.o
	g++ -g -c -std=c++11 smtlib-glue.cpp -o smtlib-glue.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_attribute.cpp -o smt_attribute.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_basic.cpp -o smt_basic.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_command.cpp -o smt_command.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_fun.cpp -o smt_fun.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_identifier.cpp -o smt_identifier.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_literal.cpp -o smt_literal.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_logic.cpp -o smt_logic.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_s_expr.cpp -o smt_s_expr.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_script.cpp -o smt_script.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_sort.cpp -o smt_sort.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_symbol_decl.cpp -o smt_symbol_decl.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_term.cpp -o smt_term.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_theory.cpp -o smt_theory.o
	g++ -g -c -std=c++11 ../smtlib/ast/smt_var.cpp -o smt_var.o
	g++ -g -c -std=c++11 ../smtlib/parser/smt_parser.cpp -o smt_parser.o
	g++ -g -c -std=c++11 ../smtlib/util/smt_logger.cpp -o smt_logger.o
	g++ -g -o parse-smtlib smtlib-flex-lexer.l.o smtlib-bison-parser.y.o smtlib-glue.o smt_attribute.o smt_basic.o smt_command.o smt_fun.o smt_identifier.o smt_literal.o smt_logic.o smt_s_expr.o smt_sort.o smt_script.o smt_symbol_decl.o smt_term.o smt_theory.o smt_var.o smt_parser.o smt_logger.o -lfl
	rm -f *.o
clean:
	rm -f smtlib-bison-parser.y.h
	rm -f smtlib-bison-parser.y.c
	rm -f smtlib-flex-lexer.l.c
	rm -f *.o
	rm -f parse-smtlib
