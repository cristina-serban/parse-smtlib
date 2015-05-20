#include <stdio.h>
#include <stdlib.h>
#include "smt_logger.h"

using namespace smtlib;

void Logger::Message(const char* msg) {
    fprintf(stdout, "slparser: %s\n", msg);
}

void Logger::Warning(const char* fun, const char* msg) {
    fprintf(stderr, "Warning in %s: %s.\n", fun, msg);
}

void Logger::Error(int level, const char* fun, const char* msg) {
    fprintf(stderr, "Error in %s: %s.\n", fun, msg);
}

void Logger::ErrorParsing(unsigned int lineL, unsigned int colL,
                         unsigned int lineR, unsigned int colR,
                         const char* filename, const char *msg) {

    fprintf(stderr, "In %s from %d:%d to %d:%d - %s\n",
            filename, lineL, colL, lineR, colR, msg);
    exit(Logger::Errors::ERR_PARSE);
}