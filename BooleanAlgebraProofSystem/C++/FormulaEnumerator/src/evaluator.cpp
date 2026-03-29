
#include "formula_enumerator/evaluator.hpp"
#include "formula_enumerator/symbols.hpp"
#include <iostream>
#include <vector>

namespace fe {
/*
 * Evaluate a prefix-encoded Boolean formula `formula` with `formula_stop`
 * entries under a particular assignment encoded in `assignment_bits`.
 */
bool is_satisfying_assignment(const Formula &formula, int formula_stop,
                              long assignment_bits) {
  std::vector<int> operand_stack;
  operand_stack.reserve(formula_stop);

  auto is_true = [&](int sym) {
    return sym == TRUE_VALUE ||
           (sym >= MIN_VARIABLE &&
            ((assignment_bits & (1L << (sym - MIN_VARIABLE))) != 0));
  };

  for (int index = formula_stop - 1; index >= 0; --index) {

    const int symbol = formula[index];

    if (symbol == NOT) {
      const int left = operand_stack.back();
      operand_stack.pop_back();

      const bool left_truth = is_true(left);

      operand_stack.push_back(left_truth ? FALSE_VALUE : TRUE_VALUE);
    } else if (symbol == OR) {
      const int right = operand_stack.back();
      operand_stack.pop_back();

      const int left = operand_stack.back();
      operand_stack.pop_back();

      const bool left_truth = is_true(left);
      const bool right_truth = is_true(right);

      operand_stack.push_back((left_truth || right_truth) ? TRUE_VALUE
                                                          : FALSE_VALUE);
    } else if (symbol == AND) {
      const int right = operand_stack.back();
      operand_stack.pop_back();

      const int left = operand_stack.back();
      operand_stack.pop_back();

      const bool left_truth = is_true(left);
      const bool right_truth = is_true(right);

      operand_stack.push_back((left_truth && right_truth) ? TRUE_VALUE
                                                          : FALSE_VALUE);
    } else {
      operand_stack.push_back(symbol);
    }
  }

  return !operand_stack.empty() && operand_stack.back() == TRUE_VALUE;
}

/*
 * Determine whether `formula` is a tautology (if `tautology` is true) or a
 * contradiction (if `tautology` is false). The function exhaustively
 * tests all assignments for the `variable_count` variables.
 */
bool is_tautology_or_contradiction(const bool tautology, const Formula &formula,
                                   const int formula_stop,
                                   const int variable_count, const int index) {
  const long limit = 1L << variable_count;

  for (long assignment_bits = 0; assignment_bits < limit; ++assignment_bits) {

    const bool satisfying =
        is_satisfying_assignment(formula, formula_stop, assignment_bits);

    if ((tautology && !satisfying) || (!tautology && satisfying)) {

      std::cout << format_formula(formula, formula_stop)
                << (tautology ? " is not a tautology."
                              : " is not a contradiction.");

      if (variable_count > 0) {
        std::cout << " Proof: ";
      }

      long bit = 1;

      for (int index = 0; index < variable_count; ++index) {
        std::cout << "x" << index << " = "
                  << ((assignment_bits & bit) == 0 ? "false" : "true");
        if (index + 1 < variable_count) {
          std::cout << ", ";
        }
        bit <<= 1;
      }

      std::cout << "\n";

      return false;
    }
  }

  std::cout << "#" << index << ": " << format_formula(formula, formula_stop)
            << (tautology ? " is a tautology." : " is a contradiction.");
  return true;
}

}
