#pragma once

#include <string>

namespace fe {

constexpr int MAX_LENGTH = 100;

constexpr int STOP = 0;
constexpr int NOT = 1;
constexpr int OR = 2;
constexpr int AND = 3;
constexpr int FALSE_VALUE = 4;
constexpr int TRUE_VALUE = 5;
constexpr int MIN_VARIABLE = 6;

inline bool is_truth_value(const int symbol) {
    return symbol == TRUE_VALUE || symbol == FALSE_VALUE;
}

inline bool is_variable(const int symbol) {
    return symbol >= MIN_VARIABLE;
}

inline bool is_boolean(const int symbol) {
    return symbol >= FALSE_VALUE;
}

inline std::string symbol_to_text(const int symbol) {
    switch (symbol) {
        case NOT:
            return "-";
        case OR:
            return "+";
        case AND:
            return "*";
        case FALSE_VALUE:
            return "F";
        case TRUE_VALUE:
            return "T";
        default:
            if (is_variable(symbol)) {
                return "x" + std::to_string(symbol - MIN_VARIABLE);
            }
            return "?";
    }
}

}
