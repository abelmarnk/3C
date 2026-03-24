#pragma once
#include <string>
#include <vector>

namespace fe {

using Formula = std::vector<int>;

int index_of_stop(const Formula &);
void fill_before_stop(Formula &, int, int = 1);
int count_variables(const Formula &, int);
bool is_valid_syntax(const Formula &, int);
std::string format_formula(const Formula &, int);

}
