#pragma once

#include <unordered_map>

#include "formula_enumerator/formula.hpp"

namespace fe {

struct SubExpression {
  int count = 0;
  int kind = 0; // 0 = Plain Variable, 1 = NOT, 2 = OR, 3 = AND
  int a = 0;
  int b = 0;
};

using VariableMap = std::unordered_map<int, SubExpression>;

void store_initial_variables(const Formula &, VariableMap &);

bool transform_by_law_at_index(Formula &, int, int, int, VariableMap &);

}
