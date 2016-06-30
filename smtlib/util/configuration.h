#ifndef PARSE_SMTLIB_CONFIGURATION_H
#define PARSE_SMTLIB_CONFIGURATION_H

#include <algorithm>
#include <string>
#include <map>

namespace smtlib {
    class Configuration {
    public:
        enum Property {
            LOC_LOGICS = 0, LOC_THEORIES, FILE_EXT_LOGIC, FILE_EXT_THEORY
        };

        static std::map<std::string, Property> PROP_NAMES;

    private:
        static const std::string TRIM_CHARS;

        static inline bool isTrimChar(char c) {
            bool value = TRIM_CHARS.find(c) != std::string::npos;
            return TRIM_CHARS.find(c) != std::string::npos;
        }

        // trim from start
        static inline std::string &ltrim(std::string &s) {
            s.erase(s.begin(), std::find_if(s.begin(), s.end(), std::not1(std::ptr_fun<char, bool>(Configuration::isTrimChar))));
            return s;
        }

        // trim from end
        static inline std::string &rtrim(std::string &s) {
            s.erase(std::find_if(s.rbegin(), s.rend(), std::not1(std::ptr_fun<char, bool>(Configuration::isTrimChar))).base(), s.end());
            return s;
        }

        // trim from both ends
        static inline std::string &trim(std::string &s) {
            return ltrim(rtrim(s));
        }

        std::map<Property, std::string> properties;

    public:
        Configuration();
        Configuration(std::string path);

        void populatePropNames();
        void loadDefaults();
        void loadFile(std::string path);

        std::string get(Property key);
    };
}

#endif //PARSE_SMTLIB_CONFIGURATION_H
