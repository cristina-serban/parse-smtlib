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

        static void Error(int level, const char *fun, const char *msg);

        static void ErrorParsing(unsigned int lineL, unsigned int colL,
                                 unsigned int lineR, unsigned int colR,
                                 const char* filename, const char *msg);
    };
}

#endif //PARSE_SMTLIB_SMT_LOGGER_H
