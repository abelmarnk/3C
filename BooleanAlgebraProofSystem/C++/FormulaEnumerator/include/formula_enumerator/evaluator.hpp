#pragma once
#include "formula_enumerator/formula.hpp"

namespace fe {

bool is_satisfying_assignment(const Formula &, int, long);
bool is_tautology_or_contradiction(bool, const Formula &, int, int, int);

}
