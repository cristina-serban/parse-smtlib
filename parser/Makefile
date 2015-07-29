code:
	bison -d smtlib-bison-parser.y -Wconflicts-sr -Wconflicts-rr
	mv smtlib-bison-parser.tab.h smtlib-bison-parser.y.h
	mv smtlib-bison-parser.tab.c smtlib-bison-parser.y.c
	flex smtlib-flex-lexer.l
	mv lex.yy.c smtlib-flex-lexer.l.c
parser:
	bison -d smtlib-bison-parser.y -Wconflicts-sr -Wconflicts-rr
	mv smtlib-bison-parser.tab.h smtlib-bison-parser.y.h
	mv smtlib-bison-parser.tab.c smtlib-bison-parser.y.c
	flex smtlib-flex-lexer.l
	mv lex.yy.c smtlib-flex-lexer.l.c
	g++ -g -c -std=c++11 smtlib-flex-lexer.l.c -o smtlib-flex-lexer.l.o
	g++ -g -c -std=c++11 smtlib-bison-parser.y.c -o smtlib-bison-parser.y.o
	g++ -g -c -std=c++11 smtlib-glue.cpp -o smtlib-glue.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_attribute.cpp -o ast_attribute.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_basic.cpp -o ast_basic.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_command.cpp -o ast_command.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_datatype.cpp -o ast_datatype.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_fun.cpp -o ast_fun.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_identifier.cpp -o ast_identifier.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_literal.cpp -o ast_literal.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_logic.cpp -o ast_logic.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_match.cpp -o ast_match.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_script.cpp -o ast_script.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_sexp.cpp -o ast_sexp.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_sort.cpp -o ast_sort.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_symbol_decl.cpp -o ast_symbol_decl.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_term.cpp -o ast_term.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_theory.cpp -o ast_theory.o
	g++ -g -c -std=c++11 ../smtlib/ast/ast_var.cpp -o ast_var.o
	g++ -g -c -std=c++11 ../smtlib/parser/smt_parser.cpp -o smt_parser.o
	g++ -g -c -std=c++11 ../smtlib/util/logger.cpp -o logger.o
	g++ -g -c -std=c++11 ../smtlib/util/global_settings.cpp -o global_settings.o
	g++ -g -o parser smtlib-flex-lexer.l.o smtlib-bison-parser.y.o \
	smtlib-glue.o ast_attribute.o ast_basic.o ast_command.o ast_datatype.o \
	ast_fun.o ast_identifier.o ast_literal.o ast_logic.o ast_match.o ast_sexp.o \
	ast_sort.o ast_script.o ast_symbol_decl.o ast_term.o ast_theory.o ast_var.o \
	smt_parser.o logger.o global_settings.o -lfl
	rm -f *.o
clean:
	rm -f smtlib-bison-parser.y.h
	rm -f smtlib-bison-parser.y.c
	rm -f smtlib-flex-lexer.l.c
	rm -f *.o
	rm -f parser