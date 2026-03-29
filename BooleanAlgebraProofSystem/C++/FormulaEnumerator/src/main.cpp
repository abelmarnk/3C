#include <climits>
#include <ctime>
#include <iostream>
#include <string>
#include <vector>

#include "formula_enumerator/enumerator.hpp"

namespace {

struct CliState {
  fe::Config config;
  bool saw_target = false;
  bool saw_proof_limit = false;
  bool saw_reduction_limit = false;
  bool saw_reduction_steps = false;
};

void print_usage(std::ostream &out) {
  out << "Usage: formula_enumerator [options]\n"
      << "  --mode target|reduction\n"
      << "  --target tautology|contradiction\n"
      << "  --symbols <int>\n"
      << "  --padding <int>\n"
      << "  --proof-limit <int>\n"
      << "  --reduction-limit <int>\n"
      << "  --reduction-steps <int>\n"
      << "  --help\n";
}

bool require_value(const std::vector<std::string> &arguments, int &index,
                   std::string &error_message) {
  if (index + 1 >= static_cast<int>(arguments.size())) {
    error_message = "Missing value for " + arguments[index] + ".";
    return false;
  }

  ++index;
  return true;
}

bool parse_int(const std::string &option, const std::string &text, int &value,
               std::string &error_message) {
  try {
    std::size_t parsed = 0;
    const long parsed_value = std::stol(text, &parsed);

    if (parsed != text.size()) {
      error_message = "Invalid integer for " + option + ": " + text;
      return false;
    }
    if (parsed_value < INT_MIN || parsed_value > INT_MAX) {
      error_message = "Integer out of range for " + option + ": " + text;
      return false;
    }

    value = static_cast<int>(parsed_value);
    return true;
  } catch (const std::exception &) {
    error_message = "Invalid integer for " + option + ": " + text;
    return false;
  }
}

bool parse_arguments(const std::vector<std::string> &arguments, CliState &state,
                     std::string &error_message) {
  for (int index = 0; index < static_cast<int>(arguments.size()); ++index) {
    const std::string &option = arguments[index];

    if (option == "--help") {
      print_usage(std::cout);
      return false;
    }

    if (!require_value(arguments, index, error_message)) {
      return false;
    }

    const std::string &value = arguments[index];

    if (option == "--mode") {
      if (value == "target") {
        state.config.mode = fe::Mode::TargetSearch;
      } else if (value == "reduction") {
        state.config.mode = fe::Mode::Reduction;
      } else {
        error_message = "Invalid value for --mode: " + value;
        return false;
      }
    } else if (option == "--target") {
      state.saw_target = true;

      if (value == "tautology") {
        state.config.target_options.find_tautologies = true;
      } else if (value == "contradiction") {
        state.config.target_options.find_tautologies = false;
      } else {
        error_message = "Invalid value for --target: " + value;
        return false;
      }
    } else if (option == "--symbols") {
      if (!parse_int(option, value, state.config.number_of_symbols,
                     error_message)) {
        return false;
      }
    } else if (option == "--padding") {
      if (!parse_int(option, value, state.config.extra_space_after_formula,
                     error_message)) {
        return false;
      }
    } else if (option == "--proof-limit") {
      state.saw_proof_limit = true;
      if (!parse_int(option, value,
                     state.config.target_options.search_proof_until_length,
                     error_message)) {
        return false;
      }
    } else if (option == "--reduction-limit") {
      state.saw_reduction_limit = true;
      if (!parse_int(option, value,
                     state.config.reduce_options.max_reduction_sequence_length,
                     error_message)) {
        return false;
      }
    } else if (option == "--reduction-steps") {
      state.saw_reduction_steps = true;
      if (!parse_int(option, value, state.config.reduce_options.reduction_steps,
                     error_message)) {
        return false;
      }
    } else {
      error_message = "Unknown option: " + option;
      return false;
    }
  }

  return true;
}

bool validate_cli_state(const CliState &state, std::string &error_message) {
  const fe::Config &config = state.config;

  if (config.number_of_symbols < 2) {
    error_message = "--symbols must be at least 2.";
    return false;
  }
  if (config.extra_space_after_formula < 0) {
    error_message = "--padding must not be negative.";
    return false;
  }
  if (config.target_options.search_proof_until_length < 1) {
    error_message = "--proof-limit must be at least 1.";
    return false;
  }
  if (config.reduce_options.max_reduction_sequence_length < 1) {
    error_message = "--reduction-limit must be at least 1.";
    return false;
  }
  if (config.reduce_options.reduction_steps < 1) {
    error_message = "--reduction-steps must be at least 1.";
    return false;
  }

  if (config.mode == fe::Mode::TargetSearch) {
    if (state.saw_reduction_limit || state.saw_reduction_steps) {
      error_message =
          "--reduction-limit and --reduction-steps are only valid with "
          "--mode reduction.";
      return false;
    }
  } else {
    if (state.saw_target || state.saw_proof_limit) {
      error_message =
          "--target and --proof-limit are only valid with --mode target.";
      return false;
    }
  }

  return true;
}

int run(const fe::Config &config) {
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

} // namespace

int main(int argc, char **argv) {
  CliState state;
  std::string error_message;
  std::vector<std::string> arguments;
  arguments.reserve(argc > 1 ? argc - 1 : 0);

  for (int index = 1; index < argc; ++index) {
    arguments.emplace_back(argv[index]);
  }

  if (!parse_arguments(arguments, state, error_message)) {
    if (error_message.empty()) {
      return 0;
    }

    std::cerr << error_message << "\n";
    print_usage(std::cerr);
    return 1;
  }

  if (!validate_cli_state(state, error_message)) {
    std::cerr << error_message << "\n";
    print_usage(std::cerr);
    return 1;
  }

  return run(state.config);
}
