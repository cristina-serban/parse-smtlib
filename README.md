# README #

Parser for version 2.5 of SMT-LIB.

## Run the parser ##
Minimum requirements for parser compilation: Flex 2.5.35 and Bison 3.0.2.

Compiling and running the parser:
```
#!
> cd parser
> make
> ./parse < test1.smt
> ./parse < test2.smt
> ./parse < test3.smt
```

Recompiling the parser:
```
#!
> cd parser
> make clean
> make
```