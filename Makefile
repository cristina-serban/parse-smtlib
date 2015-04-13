smtlib-parser:
	bison -d smtlib-parser.y -Wconflicts-sr
	mv smtlib-parser.tab.h smtlib-parser.h
	mv smtlib-parser.tab.c smtlib-parser.y.c
	flex smtlib-parser.lex
	mv lex.yy.c smtlib-parser.lex.c
	gcc -g -c smtlib-parser.lex.c -o smtlib-parser.lex.o
	gcc -g -c smtlib-parser.y.c -o smtlib-parser.y.o
	gcc -g -o smtlib-parser smtlib-parser.lex.o smtlib-parser.y.o -lfl
clean:
	rm -f smtlib-parser.h
	rm -f smtlib-parser.y.c
	rm -f smtlib-parser.lex.c
	rm -f smtlib-parser.output
	rm -f smtlib-parser.y.o
	rm -f smtlib-parser.lex.o
	rm -f smtlib-parser
