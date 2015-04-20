smtlib-parser:
	bison -d smtlib-parser.y -Wconflicts-sr
	mv smtlib-parser.tab.h smtlib-parser.h
	mv smtlib-parser.tab.c smtlib-parser.y.c
	flex smtlib-parser.l
	mv lex.yy.c smtlib-parser.l.c
	gcc -g -c smtlib-parser.l.c -o smtlib-parser.l.o
	gcc -g -c smtlib-parser.y.c -o smtlib-parser.y.o
	gcc -g -o smtlib-parser smtlib-parser.lex.o smtlib-parser.y.o -lfl
clean:
	rm -f smtlib-parser.h
	rm -f smtlib-parser.y.c
	rm -f smtlib-parser.l.c
	rm -f smtlib-parser.output
	rm -f smtlib-parser.y.o
	rm -f smtlib-parser.l.o
	rm -f smtlib-parser
