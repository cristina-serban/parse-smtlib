#ifndef PARSE_SMTLIB_SMT_LOGGER_H
#define PARSE_SMTLIB_SMT_LOGGER_H

namespace smtlib {
    class Logger {
    public:
        enum Errors {
            ERR_PARSE = 1
        };

        static void message(const char *msg);

        static void warning(const char *fun, const char *msg);

        static void error(const char *fun, const char *msg);
        
        static void syntaxError(const char *fun, const char *file, const char *msg);

        static void sortednessError(const char *fun, const char *file, const char *msg);

        static void parsingError(unsigned int rowLeft, unsigned int colLeft,
                                 unsigned int rowRight, unsigned int colRight,
                                 const char *filename, const char *msg);
    };
}

#endif //PARSE_SMTLIB_SMT_LOGGER_H
