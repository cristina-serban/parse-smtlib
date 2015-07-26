#include <cstring>
#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include "util/logger.h"
#include "smtlib/smt_execution.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

int main(int argc, char **argv) {
    shared_ptr<SmtExecutionSettings> settings = make_shared<SmtExecutionSettings>();
    vector<string> files;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--no-core") == 0) {
            settings->setCoreTheoryEnabled(false);
        } else {
            files.push_back(string(argv[i]));
        }
    }

    if (files.empty()) {
        Logger::error("main()", "No input files");
        return 1;
    }

    for (auto fileIt = files.begin(); fileIt != files.end(); fileIt++) {
        settings->setInputFromFile(*fileIt);
        SmtExecution exec(settings);
        exec.checkSortedness();
    }

    return 0;
}
