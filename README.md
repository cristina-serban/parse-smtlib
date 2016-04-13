# README #

Parser and well-sortedness checker for version 2.6 of SMT-LIB. 

The parsing is done using a generated parser based on Bison and Flex, which builds an abstract syntax tree. Various new operations can be implemented on this structure by extending the visitor classes provided. Additional syntax checks and well-sortedness checks are already implemented.

## Requirements ##
g++ 4.9.0 

Flex 2.5.35

Bison 2.5

Doxygen (optional, for documentation)

## Features and limitations ##
You can parse and check any kind of SMT-LIB files - scripts, logics or theories. 

Well-sortedness checks use the sort and function symbols declared in the theory files, which can be found in the folders `input/Theories` and `input/Logics`. If you want to add new theories or logics, put them in those folders. Make sure the filename coincides with the name of the logic or theory and that the extension is `.smt2`.

Because the program needs to parse the sort and function symbols from theory files (namely, the values of the `:sorts` and `:funs` attributes), it is unable to perform a good check on files working with infinite theories (such as BitVectors). These cases require specific implementations.

The 'Core' theory is automatically loaded. If you want to run the program without it loading 'Core' (for example, if, for some reason, you want it to parse and check the 'Core' theory file itself), specify the option `--no-core`. Example:
```
.../parse-smtlib> ./parse-smtlib --no-core input/Theories/Core.smt2
```

Datatypes and match terms are fully supported. The well-sortedness checker sees new datatypes as new sorts, and their constructors and selectors as new functions.

Small things that do not quite work yet (but will):

* Well-sortedness check for indexed identifiers;
* Well-sortedness check for annotated terms;

**Note:** The whole project was created and tested by a single person. I would be pleasantly surprised if it works perfectly on all your inputs. But if it does not or if you encounter problems, do not hesitate to contact me so I can fix the issues.

## Required files ##
**Important**: The well-sortedness checker needs to be able to find the files containing the definitions of theories and logics. Their default locations are `input/Theories` and `input/Logics`, relative to the project path. If you want to use a different working directory or simply change the location for the theories and logics, change the values of the `LOC_THEORIES` and `LOC_LOGICS` constants in `smtlib/util/global_settings.cpp` and rebuild the project.

## Building the project ##
(1) Before building the project, make sure the files `parser/smtlib-bison-parser.y.c`, `parser/smtlib-bison-parser.y.h` and `parser/smtlib-flex-lexer.l.c` have been generated.

(2) If any of the files mentioned above are not there:
```
.../parse-smtlib> cd parser
.../parse-smtlib/parser> make
.../parse-smtlib> cd ..
```

(3) Run `make` in the root folder of the project. This creates the executable `parse-smtlib` which can parse and check a list of files. 
```
.../parse-smtlib> make 
.../parse-smtlib> ./parse-smtlib input_file_path1 input_file_path2 input_file_path3 ...
```

(4) If you want to clean the executable or remaining files from a failed build, run `make clean`.
```
.../parse-smtlib> make clean
```

## Unfolding inductive predicates ##
If the input file (or files) contains definitions of inductive predicates, they can be unfolded for a specified number of times. The definitions have to respect the following format (you can find three examples in the file `/parse-smtlib/pred.smt2`):
```
(define-fun-rec predicate ((param_1 TypeP1) ... (paramn TypePn)) Bool
	(or (...)                                              ;base case
		(exists ((var1 TypeV1) ... (varn TypeVn)) (...)))  ;recursive case
)
```
There are three program arguments that you can specify in order to customize how the unfolding is done:
* `--unfold-level` - How deep should the unfolding go. Accepted values are nonnegative integers. A value of 0 (default) means that the recursive call inside the definition will be replaced by the base case.
* `--unfold-exist` - Whether the existential quantifier should be used in the unfolding or not. Accepted values are `y` (default) and `n`. If you specify a value of `n`, the existential quantifier will disappear from the definition and all existentially quantified variales will be declared as constants.
* `--unfold-path` - File to which the results will be appended. Value defaults to a file name `unfolding` in the current working directory.
* `--cvc-emp` - Specifying this will make `emp` become `(emp 0)` in the output (for compatibility with CVC4).

**Note**: At least one of these arguments has to be specified for the unfolding to take place.

Some examples:
```
.../parse-smtlib> ./parse-smtlib --unfold-level=5 --unfold-exist=n --unfold-path=pred-unfoldings.smt2 --cvc-emp pred.smt2
.../parse-smtlib> ./parse-smtlib --unfold-exist=n --unfold-path=pred-unfoldings.smt2 pred.smt2
.../parse-smtlib> ./parse-smtlib --unfold-level=3 --unfold-path=pred-unfoldings.smt2  --cvc-emp pred.smt2
.../parse-smtlib> ./parse-smtlib --unfold-level=2 --unfold-exist=y --unfold-path=pred-unfoldings.smt2 pred.smt2
```

## Recompiling and building the generated parser ##
If the files `parser/smtlib-bison-parser.y` and `parser/smtlib-flex-lexer.l` are changed, they need to be recompiled.
```
.../parse-smtlib/parser> make
```

The generated parser can also be built and used idependently (this is not required in order to run `parse-smtlib`).
```
.../parse-smtlib/parser> make parser
.../parse-smtlib/parser> ./parser < input_file_path
```

To erase generated code and/or the parser executable, run `make clean`.
```
.../parse-smtlib/parser> make clean
```

## Generating documentation ##
```
.../parse-smtlib> doxygen
```
The documentation in `html` format is generated in the `docs` folder. Open the `docs/index.html` file in a browser.
