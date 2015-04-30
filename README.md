# README #

Parser for version 2.5 of SMT-LIB.

## Running the parser ##
Minimum requirements for parser compilation: Flex 2.5.35 and Bison 3.0.2.

Compiling and running the parser:
```
#!
.../parse-smtlib/parser> make
.../parse-smtlib/parser> ./parse < input_file_path
```

Recompiling the parser:
```
#!
.../parse-smtlib/parser> make clean
.../parse-smtlib/parser> make
```

## Generating documentation ##
Doxygen is required to generate the documentation.
```
#!
.../parse-smtlib> doxygen
```
The documentation in `html` format is generated in the `docs` folder. Open the `docs/index.html` file in a browser.