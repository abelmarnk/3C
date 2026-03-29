#pragma once

#include <cstdint>

namespace fe {

enum class Mode : std::uint8_t { TargetSearch = 0, Reduction = 1 };

struct TargetOptions {
  bool find_tautologies = true;
  int search_proof_until_length = 5;
};

struct ReduceOptions {
  int max_reduction_sequence_length = 5;
  int reduction_steps = 1;
};

// Global configuration.
struct Config {
  Mode mode = Mode::TargetSearch;

  int number_of_symbols = 3;
  int extra_space_after_formula = 5;

  TargetOptions target_options;
  ReduceOptions reduce_options;
};

void enumerate_boolean_formulas(const Config &config);
void enumerate_reductions(const Config &config);

}
