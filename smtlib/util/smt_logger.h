#ifndef PARSE_SMTLIB_SMT_LOGGER_H
#define PARSE_SMTLIB_SMT_LOGGER_H

namespace smtlib {
    class Logger {
    public:
        enum Errors {
            ERR_PARSE = 1
        };

        static void Message(const char *msg);

        static void Warning(const char *fun, const char *msg);

        static void Error(const char *fun, const char *msg);
        
        static void SyntaxError(const char* fun, const char *file, const char *msg);

        static void ParsingError(unsigned int rowLeft, unsigned int colLeft,
                                 unsigned int rowRight, unsigned int colRight,
                                 const char *filename, const char *msg);
    };
}

#endif //PARSE_SMTLIB_SMT_LOGGER_H
