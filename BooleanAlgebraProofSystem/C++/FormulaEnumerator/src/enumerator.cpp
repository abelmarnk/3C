#include "formula_enumerator/enumerator.hpp"

#include <algorithm>
#include <ctime>
#include <iostream>
#include <list>
#include <utility>
#include <vector>

#include "formula_enumerator/evaluator.hpp"
#include "formula_enumerator/formula.hpp"
#include "formula_enumerator/laws.hpp"
#include "formula_enumerator/proof_search.hpp"
#include "formula_enumerator/rewriter.hpp"
#include "formula_enumerator/symbols.hpp"

namespace fe {

namespace {
/*
 * Print a single histogram bin.
 * The histogram stores identifiers (indices) for formulas that share
 * a particular property (e.g. proof length or law occurrence). This helper
 * prints each identifier prefixed with `#` separated by commas.
 */
void print_histogram_bin(const std::list<int> &histogram_bin) {
  for (const int item : histogram_bin) {
    std::cout << "#" << item << ", ";
  }
  std::cout << "\n";
}

/*
 * Produce a sorted list of non-empty histogram bins.
 * - `histogram` is a vector of lists where the index is the bin key.
 * - `max_bin_index` bounds the search (inclusive).
 * - `sequence` is filled with (bin_index, frequency) pairs.
 * Returns the number of non-empty bins stored into `sequence`.
 */
int sort_histogram(const std::vector<std::list<int>> &histogram,
                   const int max_bin_index,
                   std::vector<std::pair<int, int>> &sequence) {
  sequence.clear();

  for (int index = max_bin_index; index >= 0; --index) {
    const int frequency = static_cast<int>(histogram[index].size());
    if (frequency > 0) {
      sequence.emplace_back(index, frequency);
    }
  }

  std::stable_sort(
      sequence.begin(), sequence.end(),
      [](const auto &a, const auto &b) { return a.second < b.second; });

  return static_cast<int>(sequence.size());
}

/*
 * Print formulas that could not be proved within the configured search
 * depth (holdouts).
 */
void print_holdout_list(const std::list<Formula> &holdout_list,
                        const int f_stop) {
  int index = 0;

  for (const auto &formula : holdout_list) {
    std::cout << index << ": " << format_formula(formula, f_stop) << "\n";
    ++index;
  }
}

} // namespace

void enumerate_reductions(const Config &config) {
  const int number_of_symbols = config.number_of_symbols;
  const int padding = config.extra_space_after_formula;
  const int proof_search_limit =
      config.reduce_options.max_reduction_sequence_length;
  const int reduction_steps = config.reduce_options.reduction_steps;

  if (number_of_symbols < 2) {
    std::cout << "Number of symbols should not be less than 2.\n";
    return;
  }
  if (padding < 0) {
    std::cout << "The padding must not be negative.\n";
    return;
  }

  const int formula_length = number_of_symbols + 1 + padding;
  Formula formula;
  fill_before_stop(formula, number_of_symbols, 1);

  const int n_minus_1 = number_of_symbols - 1;
  const int max_symbol = MIN_VARIABLE + n_minus_1;

  int valid_syntax_and_labeling_count = 0;
  int reducible_count = 0;

  std::vector<std::list<int>> reduction_length_histogram(proof_search_limit +
                                                         1);
  std::vector<std::list<int>> law_histogram(LAW_COUNT);
  std::vector<std::list<int>> index_histogram(formula_length);
  std::vector<std::pair<int, int>> sort_buffer;
  std::list<Formula> holdout_list;

  Proof current_sequence;
  VariableMap variables_in_use;

  while (formula[0] <= 3) {
    const int variable_count = count_variables(formula, number_of_symbols);

    if (variable_count >= 0 && is_valid_syntax(formula, number_of_symbols)) {
      ++valid_syntax_and_labeling_count;

      const int reduction_length = brute_force_reduce_until_size(
          proof_search_limit, reduction_steps, formula, formula_length,
          current_sequence, variables_in_use);

      if (reduction_length > 0) {
        reduction_length_histogram[reduction_length].push_back(reducible_count);

        for (const auto &[law, index] : current_sequence) {
          law_histogram[law].push_back(reducible_count);
          index_histogram[index].push_back(reducible_count);
        }

        ++reducible_count;
      } else {
        holdout_list.push_back(formula);
      }
    }

    int index = n_minus_1;

    ++formula[index];

    while (formula[index] > max_symbol && index > 0) {
      formula[index] = 1;

      --index;

      ++formula[index];
    }
  }

  std::cout << "\nThere are " << valid_syntax_and_labeling_count
            << " Boolean formulas with " << number_of_symbols
            << " symbols and with valid syntax and variable labeling.\n\n";

  std::cout << "There are " << reducible_count
            << " formulas reducible by at least " << reduction_steps
            << " token(s) within a sequence length of " << proof_search_limit
            << ".\n\n";

  std::cout << "Reduction Length Histogram:\n\n";

  for (int index = 1; index <= proof_search_limit; ++index) {
    const int frequency =
        static_cast<int>(reduction_length_histogram[index].size());

    std::cout << "\t" << frequency
              << " formulas have a minimal reduction length of " << index;

    if (frequency > 0) {
      std::cout << ":\n\t";
      print_histogram_bin(reduction_length_histogram[index]);
    } else {
      std::cout << "\n";
    }
    std::cout << "\n";
  }

  std::cout << "Most common to least common minimal reduction lengths (with "
               "non-zero frequency):\n";
  int frequency_count = sort_histogram(reduction_length_histogram,
                                       proof_search_limit, sort_buffer);

  for (int idx = frequency_count - 1; idx >= 0; --idx) {
    std::cout << sort_buffer[idx].first;
    if (idx > 0) {
      std::cout << ", ";
    }
  }

  std::cout
      << "\n\nHistogram of Boolean Algebra Law Occurrences in reductions:\n\n";
  for (int i = 0; i < LAW_COUNT; ++i) {
    const int frequency = static_cast<int>(law_histogram[i].size());

    std::cout << "\tThe " << LAW_NAMES[i] << " law occurred " << frequency
              << " times";

    if (frequency > 0) {
      std::cout << " in the minimal reductions of the following Boolean "
                   "formulas:\n\t";
      print_histogram_bin(law_histogram[i]);
    } else {
      std::cout << "\n";
    }
    std::cout << "\n";
  }

  std::cout << "Most common to least common Boolean algebra laws (with "
               "non-zero frequency):\n";

  frequency_count = sort_histogram(law_histogram, LAW_COUNT - 1, sort_buffer);

  for (int idx = frequency_count - 1; idx >= 0; --idx) {
    std::cout << LAW_NAMES[sort_buffer[idx].first];
    if (idx > 0) {
      std::cout << ", ";
    }
  }

  std::cout
      << "\n\nHistogram of Reduction Steps per Boolean Formula Index:\n\n";

  for (int index = 0; index < formula_length; ++index) {
    const int frequency = static_cast<int>(index_histogram[index].size());

    std::cout << "\t" << frequency
              << " reduction steps occurred at Boolean formula index " << index;

    if (frequency > 0) {
      std::cout << " in the minimal reductions of the following Boolean "
                   "formulas:\n\t";
      print_histogram_bin(index_histogram[index]);
    } else {
      std::cout << "\n";
    }
    std::cout << "\n";
  }

  std::cout << "Most common to least common Boolean formula indices (with "
               "non-zero frequency):\n";

  frequency_count =
      sort_histogram(index_histogram, formula_length - 1, sort_buffer);

  for (int idx = frequency_count - 1; idx >= 0; --idx) {
    std::cout << sort_buffer[idx].first;
    if (idx > 0) {
      std::cout << ", ";
    }
  }

  std::cout << "\n\n";

  if (!holdout_list.empty()) {
    std::cout << holdout_list.size()
              << " holdouts have a minimal reduction length exceeding "
              << proof_search_limit << ":\n";

    print_holdout_list(holdout_list, number_of_symbols);

    std::cout << "\n";
  }
}

/*
 * Iterates over all polish formulas of length `number_of_symbols` with a
 * sentinel `STOP` at the end and optional padding space. For each syntactically
 * valid, properly-labeled formula it:
 *  - Checks whether it is a tautology or contradiction.
 *  - Runs the brute-force proof search up to `search_proof_until_length`.
 *  - Accumulates histograms for proof lengths, laws used, and indices.
 *  - Records formulas whose minimal proof exceeds the search limit (holdouts).
 */
void enumerate_boolean_formulas(const Config &config) {
  const int number_of_symbols = config.number_of_symbols;
  const int padding = config.extra_space_after_formula;
  const bool should_find_tautology = config.target_options.find_tautologies;
  const int proof_search_limit =
      config.target_options.search_proof_until_length;

  if (number_of_symbols < 2) {
    std::cout << "Number of symbols should not be less than 2.\n";
    return;
  }
  if (padding < 0) {
    std::cout << "The padding must not be negative.\n";
    return;
  }

  const int formula_length = number_of_symbols + 1 + padding;
  Formula formula;
  fill_before_stop(formula, number_of_symbols, 1);

  const int target = should_find_tautology ? TRUE_VALUE : FALSE_VALUE;
  const int n_minus_1 = number_of_symbols - 1;
  const int max_symbol = MIN_VARIABLE + n_minus_1;

  int valid_syntax_and_labeling_count = 0;
  int tautology_or_unsat_count = 0;
  Formula formula_with_longest_proof(number_of_symbols + 1, STOP);
  int max_proof_length = 0;

  std::vector<std::list<int>> proof_length_histogram(proof_search_limit + 1);
  std::vector<std::list<int>> law_histogram(LAW_COUNT);
  std::vector<std::list<int>> index_histogram(formula_length);
  std::vector<std::pair<int, int>> sort_buffer;
  std::list<Formula> holdout_list;

  Proof current_proof;
  Proof longest_proof;
  VariableMap variables_in_use;

  while (formula[0] <= 3) {
    const int variable_count = count_variables(formula, number_of_symbols);

    if (variable_count >= 0 && is_valid_syntax(formula, number_of_symbols)) {
      ++valid_syntax_and_labeling_count;

      if (is_tautology_or_contradiction(should_find_tautology, formula,
                                        number_of_symbols, variable_count,
                                        tautology_or_unsat_count)) {
        const int proof_length = brute_force_proof_until_size(
            proof_search_limit, target, formula, formula_length, current_proof,
            variables_in_use);

        if (proof_length > max_proof_length) {
          formula_with_longest_proof = formula;
          longest_proof = current_proof;
          max_proof_length = proof_length;
        }

        if (proof_length > 0) {
          proof_length_histogram[proof_length].push_back(
              tautology_or_unsat_count);
          for (const auto &[law, index] : current_proof) {
            law_histogram[law].push_back(tautology_or_unsat_count);
            index_histogram[index].push_back(tautology_or_unsat_count);
          }
        } else {
          holdout_list.push_back(formula);
        }

        ++tautology_or_unsat_count;
      }
    }

    int index = n_minus_1;

    ++formula[index];

    while (formula[index] > max_symbol && index > 0) {
      formula[index] = 1;

      --index;

      ++formula[index];
    }
  }

  std::cout << "\nThere are " << valid_syntax_and_labeling_count
            << " Boolean formulas with " << number_of_symbols
            << " symbols and with valid syntax and variable labeling.\n\n"
            << "There are " << tautology_or_unsat_count
            << (should_find_tautology ? " tautologies" : " contradictions")
            << " with " << number_of_symbols << " symbols.\n\n";

  std::cout << "Boolean formula with the longest proof: "
            << format_formula(formula_with_longest_proof, number_of_symbols)
            << "\nLongest proof: [";

  for (std::size_t index = 0; index < longest_proof.size(); ++index) {
    std::cout << LAW_NAMES[longest_proof[index].first] << " at "
              << longest_proof[index].second;

    if (index + 1 < longest_proof.size()) {
      std::cout << ", ";
    }
  }

  std::cout << "]\nMax proof length = " << max_proof_length
            << "\n\nProof Length Histogram:\n\n";

  for (int index = 1; index <= proof_search_limit; ++index) {
    const int frequency =
        static_cast<int>(proof_length_histogram[index].size());

    std::cout << "\t" << frequency
              << (should_find_tautology ? " tautologies" : " contradictions")
              << " have a minimal proof length of " << index;

    if (frequency > 0) {
      std::cout << ":\n\t";
      print_histogram_bin(proof_length_histogram[index]);
    } else {
      std::cout << "\n";
    }
    std::cout << "\n";
  }

  std::cout << "Most common to least common minimal proof lengths (with "
               "non-zero frequency):\n";
  int frequency_count =
      sort_histogram(proof_length_histogram, proof_search_limit, sort_buffer);

  for (int index = frequency_count - 1; index >= 0; --index) {
    std::cout << sort_buffer[index].first;
    if (index > 0) {
      std::cout << ", ";
    }
  }

  std::cout << "\n\nHistogram of Boolean Algebra Law Occurrences:\n\n";
  for (int index = 0; index < LAW_COUNT; ++index) {
    const int frequency = static_cast<int>(law_histogram[index].size());

    std::cout << "\tThe " << LAW_NAMES[index] << " law occurred " << frequency
              << " times";

    if (frequency > 0) {
      std::cout
          << " in the minimal proofs of the following Boolean formulas:\n\t";
      print_histogram_bin(law_histogram[index]);
    } else {
      std::cout << "\n";
    }
    std::cout << "\n";
  }

  std::cout << "Most common to least common Boolean algebra laws (with "
               "non-zero frequency):\n";

  frequency_count = sort_histogram(law_histogram, LAW_COUNT - 1, sort_buffer);

  for (int index = frequency_count - 1; index >= 0; --index) {
    std::cout << LAW_NAMES[sort_buffer[index].first];
    if (index > 0) {
      std::cout << ", ";
    }
  }

  std::cout << "\n\nHistogram of Proof Steps per Boolean Formula Index:\n\n";

  for (int index = 0; index < formula_length; ++index) {
    const int frequency = static_cast<int>(index_histogram[index].size());

    std::cout << "\t" << frequency
              << " proof steps occurred at Boolean formula index " << index;

    if (frequency > 0) {
      std::cout
          << " in the minimal proofs of the following Boolean formulas:\n\t";
      print_histogram_bin(index_histogram[index]);
    } else {
      std::cout << "\n";
    }
    std::cout << "\n";
  }

  std::cout << "Most common to least common Boolean formula indices (with "
               "non-zero frequency):\n";

  frequency_count =
      sort_histogram(index_histogram, formula_length - 1, sort_buffer);

  for (int index = frequency_count - 1; index >= 0; --index) {
    std::cout << sort_buffer[index].first;
    if (index > 0) {
      std::cout << ", ";
    }
  }

  std::cout << "\n\n";

  if (!holdout_list.empty()) {
    std::cout << holdout_list.size()
              << " holdouts have a minimal proof length exceeding "
              << proof_search_limit << ":\n";

    print_holdout_list(holdout_list, number_of_symbols);

    std::cout << "\n";
  }
}

} // namespace fe
