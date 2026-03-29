#include "formula_enumerator/formula.hpp"
#include "formula_enumerator/symbols.hpp"
#include <sstream>
#include <vector>

namespace fe {

/*
 * Returns the index of the `STOP` symbol, or -1 if not found.
 */
int index_of_stop(const Formula &formula) {
  for (int index = 0; index < static_cast<int>(formula.size()); ++index) {
    if (formula[index] == STOP) {
      return index;
    }
  }
  return -1;
}

/*
 * Initialize a formula of length `n` + 1 where the first `n` slots
 * are filled with `element` and the last position contains `STOP`.
 */
void fill_before_stop(Formula &formula, int n, int element) {
  formula.assign(n + 1, element);
  formula[n] = STOP;
}

/*
 * Count distinct variable tokens present in the formula up to `formula_stop`.
 * Returns -1 if the variable labels are not contiguous from x0 upward.
 */
int count_variables(const Formula &formula, const int formula_stop) {

  std::vector<bool> variable_checklist(formula_stop + 1, false);

  int variable_count = 0;

  for (int index = 0; index < formula_stop; ++index) {
    const int variable = formula[index] - MIN_VARIABLE;

    if (variable >= 0) {
      if (variable >= static_cast<int>(variable_checklist.size())) {
        variable_checklist.resize(variable + 1, false);
      }

      if (!variable_checklist[variable]) {
        variable_checklist[variable] = true;
        ++variable_count;
      }
    }
  }

  for (int variable = 0; variable < variable_count; ++variable) {
    if (variable >= static_cast<int>(variable_checklist.size()) ||
        !variable_checklist[variable]) {
      return -1;
    }
  }

  return variable_count;
}

/*
 * This asserts that the formula is properly encoded in polish scheme.
 */
bool is_valid_syntax(const Formula &formula, const int formula_stop) {

  std::vector<int> operand_stack;
  operand_stack.reserve(formula_stop);

  for (int index = formula_stop - 1; index >= 0; --index) {

    const int symbol = formula[index];

    if (symbol == NOT) {
      if (operand_stack.empty()) {
        return false;
      }

      // This is not really necessary, but it's left for clarity
      operand_stack.pop_back();
      operand_stack.push_back(0);
    } else if (symbol == OR || symbol == AND) {
      if (operand_stack.size() < 2) {
        return false;
      }

      operand_stack.pop_back();

      // This is not really necessary, but it's left for clarity
      operand_stack.pop_back();
      operand_stack.push_back(0);
    } else {

      operand_stack.push_back(0);
    }
  }

  return operand_stack.size() == 1;
}

/*
 * Produce a human readable representation of a formula showing both the
 * numeric token sequence and the textual operator/variable names.
 */
std::string format_formula(const Formula &formula, int formula_stop) {
  std::ostringstream out;
  out << "{";

  for (int index = 0; index < formula_stop; ++index) {
    out << formula[index];
    if (index + 1 < formula_stop) {
      out << ", ";
    }
  }

  out << "} = [";

  for (int index = 0; index < formula_stop; ++index) {
    out << symbol_to_text(formula[index]);
    if (index + 1 < formula_stop) {
      out << " ";
    }
  }

  out << "]";

  return out.str();
}

} // namespace fe
