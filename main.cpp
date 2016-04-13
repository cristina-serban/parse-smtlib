#include <cstring>
#include <iostream>
#include <memory>
#include <vector>
#include <regex>
#include "smtlib/util/logger.h"
#include "smtlib/smt_execution.h"

using namespace std;
using namespace smtlib;
using namespace smtlib::ast;

int main(int argc, char **argv) {
    shared_ptr<SmtExecutionSettings> settings = make_shared<SmtExecutionSettings>();
    vector<string> files;

    regex unfoldLevelRegex("--unfold-level=(.*)");
    regex unfoldOutputPath("--unfold-path=(\\\")?(.*)(\\\")?");

    bool unfold = false;

    for (int i = 1; i < argc; i++) {
        smatch sm;

        if (strcmp(argv[i], "--no-core") == 0) {
            settings->setCoreTheoryEnabled(false);
        } else if (strcmp(argv[i], "--unfold-exist=y") == 0) {
            settings->setUnfoldExistential(true);
            unfold = true;
        } else if (strcmp(argv[i], "--unfold-exist=n") == 0) {
            settings->setUnfoldExistential(false);
            unfold = true;
        } else if (strcmp(argv[i], "--cvc-emp") == 0) {
            settings->setCvcEmp(true);
        } else if (regex_match(string(argv[i]), sm, unfoldLevelRegex)) {
            if (sm.size() == 2) {
                int level = stoi(sm[1].str().c_str());
                if (level >= 0) {
                    settings->setUnfoldLevel(level);
                    unfold = true;
                } else {
                    Logger::error("main()", "Negative value for unfolding level");
                }
            } else {
                Logger::error("main()", "Invalid value for unfolding level");
            }
        } else if (regex_match(string(argv[i]), sm, unfoldOutputPath)) {
            if (sm.size() == 4) {
                    settings->setUnfoldOutputPath(string(sm[2].str().c_str()));
                unfold = true;
            } else {
                Logger::error("main()", "Invalid value for unfolding output path");
            }
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

        if (unfold) {
            exec.unfoldPredicates();
        } else {
            exec.checkSortedness();
        }
    }

    return 0;
}
