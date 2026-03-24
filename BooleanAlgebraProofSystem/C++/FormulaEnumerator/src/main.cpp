#include <ctime>
#include <iostream>

#include "formula_enumerator/enumerator.hpp"

int main() {
  // Uses default program configuration
  fe::Config config;

  const std::clock_t start_time = std::clock();
  if (config.mode == fe::Mode::TargetSearch) {
    fe::enumerate_boolean_formulas(config);
  } else {
    fe::enumerate_reductions(config);
  }
  const std::clock_t finish_time = std::clock();

  std::cout << "RUNTIME: "
            << static_cast<double>(finish_time - start_time) / CLOCKS_PER_SEC
            << " s\n";
  return 0;
}
