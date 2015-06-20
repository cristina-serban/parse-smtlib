#include <stdio.h>
#include <stdlib.h>
#include "smt_logger.h"

using namespace smtlib;

void Logger::Message(const char* msg) {
    fprintf(stdout, "%s\n", msg);
}

void Logger::Warning(const char* fun, const char* msg) {
    fprintf(stderr, "Warning in %s: %s.\n", fun, msg);
}

void Logger::Error(const char *fun, const char *msg) {
    fprintf(stderr, "Error in %s: %s.\n", fun, msg);
}

void Logger::SyntaxError(const char* fun, const char *file, const char *msg) {
    fprintf(stderr, "%s: Syntax errors in file %s\n%s", fun, file, msg);
}

void Logger::ParsingError(unsigned int rowLeft, unsigned int colLeft,
                          unsigned int rowRight, unsigned int colRight,
                          const char *filename, const char *msg) {

    fprintf(stderr, "In %s from %d:%d to %d:%d - %s\n",
            filename, rowLeft, colLeft, rowRight, colRight, msg);
    exit(Logger::Errors::ERR_PARSE);
}