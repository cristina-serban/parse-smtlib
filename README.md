# README #

Parser and well-sortedness checker for version 2.6 of SMT-LIB. 

The parsing is done using a generated parser based on Bison and Flex, which builds an abstract syntax tree. Various new operations can be implemented on this structure by extending the visitor classes provided. Additional syntax checks and well-sortedness checks are already implemented.

## Requirements ##
g++ 4.9.0 

Flex 2.5

Bison 3.0.2

Doxygen (optional, for documentation)

## Features and limitations ##
You can parse and check any kind of SMT-LIB files - scripts, logics or theories. 

Well-sortedness checks use the sort and function symbols declared in the theory files, which can be found in the folders `input/Theories` and `input/Logics`. If you want to add new theories or logics, put them in those folders. Make sure the filename coincides with the name of the logic or theory and that the extension is `.smt2`.

Because the program needs to parse the sort and function symbols from theory files (namely, the values of the `:sorts` and `:funs` attributes), it is unable to perform a good check on files working with infinite theories (such as BitVectors). These cases require specific implementations.

The 'Core' theory is automatically loaded. If you want to run the program without it loading 'Core' (for example, if, for some reason, you want it to parse and check the 'Core' theory file itself), specify the option `--no-core`. Example:
```
#!
.../parse-smtlib> ./parse-smtlib --no-core input/Theories/Core.smt2
```

Datatypes and match terms are fully supported. The well-sortedness checker sees new datatypes as new sorts, and their constructors and selectors as new functions.

Small things that do not quite work yet (but will):

* Well-sortedness check for indexed identifiers;
* Well-sortedness check for annotated terms;

**Note:** The whole project was created and tested by a single person. I would be pleasantly surprised if it works perfectly on all your inputs. But if it does not or if you encounter problems, do not hesitate to contact me so I can fix the issues.

## Building the project ##
(1) Before building the project, make sure the files `parser/smtlib-bison-parser.y.c`, `parser/smtlib-bison-parser.y.h` and `parser/smtlib-flex-lexer.l.c` have been generated.

(2) If any of the files mentioned above are not there:
```
#!
.../parse-smtlib> cd parser
.../parse-smtlib/parser> make
.../parse-smtlib> cd ..
```

(3) Run `make` in the root folder of the project. This creates the executable `parse-smtlib` which can parse and check a list of files. 
```
#!
.../parse-smtlib> make 
.../parse-smtlib> ./parse-smtlib input_file_path1 input_file_path2 input_file_path3 ...
```

(4) If you want to clean the executable or remaining files from a failed build, run `make clean`.
```
#!
.../parse-smtlib> make clean
```

## Recompiling and building the generated parser ##
If the files `parser/smtlib-bison-parser.y` and `parser/smtlib-flex-lexer.l` are changed, they need to be recompiled.
```
#!
.../parse-smtlib/parser> make
```

The generated parser can also be built and used idependently (this is not required in order to run `parse-smtlib`).
```
#!
.../parse-smtlib/parser> make parser
.../parse-smtlib/parser> ./parser < input_file_path
```

To erase generated code and/or the parser executable, run `make clean`.
```
#!
.../parse-smtlib/parser> make clean
```

## Generating documentation ##
```
#!
.../parse-smtlib> doxygen
```
The documentation in `html` format is generated in the `docs` folder. Open the `docs/index.html` file in a browser.