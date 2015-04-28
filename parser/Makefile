smtlib-parser:
	bison -d smtlib-parser.y -Wconflicts-sr
	mv smtlib-parser.tab.h smtlib-parser.h
	mv smtlib-parser.tab.c smtlib-parser.y.c
	flex smtlib-parser.l
	mv lex.yy.c smtlib-parser.l.c
	g++ -g -c smtlib-parser.l.c -o smtlib-parser.l.o
	g++ -g -c smtlib-parser.y.c -o smtlib-parser.y.o
	g++ -g -c -std=c++11 smtlib-glue.cpp -o smtlib-glue.o
	g++ -g -c -std=c++11 ../smt/ast/smt_attribute.cpp -o smt_attribute.o
	g++ -g -c -std=c++11 ../smt/ast/smt_basic.cpp -o smt_basic.o
	g++ -g -c -std=c++11 ../smt/ast/smt_command.cpp -o smt_command.o
	g++ -g -c -std=c++11 ../smt/ast/smt_fun.cpp -o smt_fun.o
	g++ -g -c -std=c++11 ../smt/ast/smt_identifier.cpp -o smt_identifier.o
	g++ -g -c -std=c++11 ../smt/ast/smt_literal.cpp -o smt_literal.o
	g++ -g -c -std=c++11 ../smt/ast/smt_logic.cpp -o smt_logic.o
	g++ -g -c -std=c++11 ../smt/ast/smt_s_expr.cpp -o smt_s_expr.o
	g++ -g -c -std=c++11 ../smt/ast/smt_script.cpp -o smt_script.o
	g++ -g -c -std=c++11 ../smt/ast/smt_sort.cpp -o smt_sort.o
	g++ -g -c -std=c++11 ../smt/ast/smt_symbol_decl.cpp -o smt_symbol_decl.o
	g++ -g -c -std=c++11 ../smt/ast/smt_term.cpp -o smt_term.o
	g++ -g -c -std=c++11 ../smt/ast/smt_theory.cpp -o smt_theory.o
	g++ -g -c -std=c++11 ../smt/ast/smt_var.cpp -o smt_var.o
	g++ -g -o smtlib-parser smtlib-parser.l.o smtlib-parser.y.o smtlib-glue.o smt_attribute.o smt_basic.o smt_command.o smt_fun.o smt_identifier.o smt_literal.o smt_logic.o smt_s_expr.o smt_sort.o smt_script.o smt_symbol_decl.o smt_term.o smt_theory.o smt_var.o -lfl
	rm -f *.o
clean:
	rm -f smtlib-parser.h
	rm -f smtlib-parser.y.c
	rm -f smtlib-parser.l.c
	rm -f smtlib-parser.output
	rm -f *.o
	rm -f smtlib-parser
