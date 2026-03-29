#include <functional>
#include <iostream>
#include <sstream>
#include <string>

#include "formula_enumerator/enumerator.hpp"
#include "formula_enumerator/evaluator.hpp"
#include "formula_enumerator/formula.hpp"
#include "formula_enumerator/proof_search.hpp"
#include "formula_enumerator/rewriter.hpp"
#include "formula_enumerator/symbols.hpp"

namespace {

using fe::Formula;

class ScopedStreamRedirect {
public:
  ScopedStreamRedirect(std::ostream &stream, std::streambuf &replacement)
      : stream_(stream), previous_(*stream.rdbuf(&replacement)) {}

  ~ScopedStreamRedirect() { stream_.get().rdbuf(&previous_.get()); }

  ScopedStreamRedirect(const ScopedStreamRedirect &) = delete;
  ScopedStreamRedirect &operator=(const ScopedStreamRedirect &) = delete;

private:
  std::reference_wrapper<std::ostream> stream_;
  std::reference_wrapper<std::streambuf> previous_;
};

bool expect(const bool condition, const std::string &message) {
  if (!condition) {
    std::cerr << "Test failure: " << message << "\n";
    return false;
  }

  return true;
}

std::string capture_output(const std::function<void()> &action) {
  std::ostringstream captured;
  ScopedStreamRedirect redirect(std::cout, *captured.rdbuf());
  action();
  return captured.str();
}

bool test_variable_labeling() {
  const Formula contiguous = {fe::OR, fe::MIN_VARIABLE, fe::TRUE_VALUE,
                              fe::STOP};
  const Formula gap = {fe::OR, fe::MIN_VARIABLE + 1, fe::TRUE_VALUE, fe::STOP};

  return expect(fe::count_variables(contiguous, 3) == 1,
                "contiguous variables should be counted") &&
         expect(fe::count_variables(gap, 3) == -1,
                "gap-labeled variables should be rejected");
}

bool test_double_negation_tautology() {
  const Formula formula = {fe::NOT, fe::NOT, fe::TRUE_VALUE, fe::STOP};
  fe::Proof proof;
  fe::VariableMap variables_in_use;
  const int max_formula_length = 9;

  const bool is_tautology = [&] {
    bool result = false;
    capture_output([&] {
      result = fe::is_tautology_or_contradiction(
          true, formula, 3, fe::count_variables(formula, 3), 0);
    });
    return result;
  }();

  int proof_length = -1;
  capture_output([&] {
    proof_length = fe::brute_force_proof_until_size(5, fe::TRUE_VALUE, formula,
                                                    max_formula_length, proof,
                                                    variables_in_use);
  });

  return expect(is_tautology, "[- - T] should be a tautology") &&
         expect(proof_length == 1, "[- - T] should have a one-step proof");
}

bool test_tautology_with_variable() {
  const Formula formula = {fe::OR, fe::TRUE_VALUE, fe::MIN_VARIABLE, fe::STOP};
  fe::Proof proof;
  fe::VariableMap variables_in_use;
  const int variable_count = fe::count_variables(formula, 3);

  bool is_tautology = false;
  capture_output([&] {
    is_tautology =
        fe::is_tautology_or_contradiction(true, formula, 3, variable_count, 0);
  });

  int proof_length = -1;
  capture_output([&] {
    proof_length = fe::brute_force_proof_until_size(5, fe::TRUE_VALUE, formula,
                                                    9, proof, variables_in_use);
  });

  return expect(variable_count == 1,
                "[+ T x0] should count exactly one variable") &&
         expect(is_tautology, "[+ T x0] should be a tautology") &&
         expect(proof_length > 0 && proof_length <= 5,
                "[+ T x0] should have a proof within the configured depth");
}

bool test_single_step_reduction() {
  const Formula formula = {fe::AND, fe::MIN_VARIABLE, fe::TRUE_VALUE, fe::STOP};
  fe::Proof proof;
  fe::VariableMap variables_in_use;
  int reduction_length = -1;

  capture_output([&] {
    reduction_length = fe::brute_force_reduce_until_size(
        5, 1, formula, 9, proof, variables_in_use);
  });

  return expect(reduction_length == 1,
                "[* x0 T] should be reducible in one step");
}

bool test_default_enumerator_regression() {
  fe::Config config;

  const std::string output =
      capture_output([&] { fe::enumerate_boolean_formulas(config); });

  return expect(output.find("There are 25 Boolean formulas with 3 symbols and "
                            "with valid syntax and variable labeling.") !=
                    std::string::npos,
                "default enumeration should reject gap-labeled formulas") &&
         expect(output.find("There are 7 tautologies with 3 symbols.") !=
                    std::string::npos,
                "default tautology totals should match the corrected search "
                "space") &&
         expect(output.find("[+ T x1]") == std::string::npos,
                "gap-labeled formulas should not appear in the default run");
}

} // namespace

int main() {
  const bool ok =
      test_variable_labeling() && test_double_negation_tautology() &&
      test_tautology_with_variable() && test_single_step_reduction() &&
      test_default_enumerator_regression();

  if (!ok) {
    return 1;
  }

  std::cout << "All FormulaEnumerator tests passed.\n";
  return 0;
}
