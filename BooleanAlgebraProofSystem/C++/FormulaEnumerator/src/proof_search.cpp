#include "formula_enumerator/proof_search.hpp"

#include <algorithm>
#include <iostream>

#include "formula_enumerator/laws.hpp"
#include "formula_enumerator/rewriter.hpp"
#include "formula_enumerator/symbols.hpp"

namespace fe {

/*
 * Apply a candidate proof sequence to `formula` and determine
 * whether the sequence reduces the formula to the requested `target`
 * (TRUE_VALUE or FALSE_VALUE) within the constraints of `max_formula_length`.
 */
bool is_proof_sequence(const Formula &formula, const int max_formula_length,
                       const Proof &sequence, const int target,
                       VariableMap &variables_in_use) {

  const int formula_stop = index_of_stop(formula);

  if (formula_stop < 1 || sequence.empty() ||
      (target != TRUE_VALUE && target != FALSE_VALUE)) {
    return false;
  }

  store_initial_variables(formula, variables_in_use);

  Formula editable = formula;

  for (const auto &[law, index] : sequence) {
    if (!transform_by_law_at_index(editable, max_formula_length, law, index,
                                   variables_in_use)) {
      return false;
    }

    if (editable.size() >= 2 && editable[0] == target && editable[1] == STOP) {
      return true;
    }
  }

  return false;
}

namespace {

bool brute_force_of_size(int proof_sequence_length, int target,
                         const Formula &formula, int max_formula_length,
                         Proof &proof_sequence, VariableMap &variables_in_use) {

  proof_sequence.assign(proof_sequence_length, {0, 0});

  const int last_law = LAW_COUNT - 1;

  const int last_index_in_formula =
      max_formula_length - 2; // cover the full padded search capacity

  const auto max_law_at = [&](const int step_index) {
    if (step_index == proof_sequence_length - 1) {
      return std::min(last_law, SUBSTITUTION - 1);
    }
    return last_law;
  };

  if (proof_sequence_length <= 0 || last_index_in_formula < 0) {
    return false;
  }

  /*
   * Exhaustive mixed-radix enumeration over Proof sequences of length
   * `proof_sequence_length`. Each step is a pair (`law`, `index`).
   * We treat the pair as a two-digit mixed-radix counter where `index` ranges
   * 0..`last_index_in_formula` and `law` ranges 0..max_law_at(`step`).
   * We increment the least-significant position (the final step) first
   * and carry left as needed.
   *
   * For each candidate we call `is_proof_sequence` to check whether the
   * sequence successfully reduces `formula` to `target`.
   */
  while (true) {
    if (is_proof_sequence(formula, max_formula_length, proof_sequence, target,
                          variables_in_use)) {
      return true;
    }

    bool advanced = false;

    for (int proof_index = proof_sequence_length - 1; proof_index >= 0;
         --proof_index) {
      auto &[law, index] = proof_sequence[proof_index];

      // Advance index first (least significant)
      ++index;

      if (index <= last_index_in_formula) {

        // Reset lower-order positions after the increment
        for (int proof_index_inner = proof_index + 1;
             proof_index_inner < proof_sequence_length; ++proof_index_inner) {
          proof_sequence[proof_index_inner] = {0, 0};
        }

        advanced = true;
        break;
      }

      index = 0;

      // Index overflowed -> advance law at this position
      ++law;

      if (law <= max_law_at(proof_index)) {
        for (int proof_index_inner = proof_index + 1;
             proof_index_inner < proof_sequence_length; ++proof_index_inner) {
          proof_sequence[proof_index_inner] = {0, 0};
        }
        advanced = true;
        break;
      }

      // Law also overflowed -> set to zero and carry left
      law = 0;
    }

    if (!advanced) {
      // We have carried past the most-significant digit, exhausted all
      // combinations and found no valid proof.
      return false;
    }
  }
}

} // namespace

/*
 * Incrementally search for a minimal proof up to length
 * `max_proof_sequence_length`. For each candidate length`proof_sequence_length`
 * (starting at 1) call the exhaustive enumerator `brute_force_of_size`. On
 * success, print the human readable representation of the found proof and
 * return its length. If no proof is found for any `proof_sequence_length <=
 * max_proof_sequence_length`, indicate failure with a printed message and
 * return -1.
 */
int brute_force_proof_until_size(const int max_proof_sequence_length,
                                 const int target, const Formula &formula,
                                 const int max_formula_length,
                                 Proof &proof_sequence,
                                 VariableMap &variables_in_use) {

  for (int proof_sequence_length = 1;
       proof_sequence_length <= max_proof_sequence_length;
       ++proof_sequence_length) {
    if (brute_force_of_size(proof_sequence_length, target, formula,
                            max_formula_length, proof_sequence,
                            variables_in_use)) {

      auto print_proof = [&](const Proof &pseq, int len) {
        std::cout << " Proof of length " << len << ": [";
        for (int proof_index = 0; proof_index < len; ++proof_index) {
          const auto &step = pseq[proof_index];
          std::cout << LAW_NAMES[step.first] << " at " << step.second;
          if (proof_index + 1 < len) {
            std::cout << ", ";
          }
        }
        std::cout << "]\n";
      };

      print_proof(proof_sequence, proof_sequence_length);

      return proof_sequence_length;
    }
  }

  std::cout << " No proof found\n";
  return -1;
}

namespace {

bool is_reduction_sequence(const Formula &formula, int max_formula_length,
                           const Proof &sequence, int reduction_steps,
                           VariableMap &variables_in_use) {

  const int original_stop = index_of_stop(formula);

  if (original_stop < 1 || sequence.empty() || reduction_steps <= 0) {
    return false;
  }

  store_initial_variables(formula, variables_in_use);

  Formula editable = formula;

  for (const auto &[law, index] : sequence) {
    if (!transform_by_law_at_index(editable, max_formula_length, law, index,
                                   variables_in_use)) {
      return false;
    }
  }

  const int new_stop = index_of_stop(editable);

  return (original_stop - new_stop) >= reduction_steps;
}

bool brute_force_reduce_of_size(int proof_sequence_length, int reduction_steps,
                                const Formula &formula, int max_formula_length,
                                Proof &proof_sequence,
                                VariableMap &variables_in_use) {

  proof_sequence.assign(proof_sequence_length, {0, 0});

  const int last_law = LAW_COUNT - 1;

  const int last_index_in_formula =
      max_formula_length - 2; // cover the full padded search capacity

  const auto max_law_at = [&](const int step_index) {
    if (step_index == proof_sequence_length - 1) {
      return std::min(last_law, SUBSTITUTION - 1);
    }
    return last_law;
  };

  if (proof_sequence_length <= 0 || last_index_in_formula < 0) {
    return false;
  }

  while (true) {
    if (is_reduction_sequence(formula, max_formula_length, proof_sequence,
                              reduction_steps, variables_in_use)) {
      return true;
    }

    bool advanced = false;

    for (int proof_index = proof_sequence_length - 1; proof_index >= 0;
         --proof_index) {
      auto &[law, index] = proof_sequence[proof_index];

      ++index;

      if (index <= last_index_in_formula) {
        for (int proof_index_inner = proof_index + 1;
             proof_index_inner < proof_sequence_length; ++proof_index_inner) {
          proof_sequence[proof_index_inner] = {0, 0};
        }

        advanced = true;
        break;
      }

      index = 0;

      ++law;

      if (law <= max_law_at(proof_index)) {
        for (int proof_index_inner = proof_index + 1;
             proof_index_inner < proof_sequence_length; ++proof_index_inner) {
          proof_sequence[proof_index_inner] = {0, 0};
        }
        advanced = true;
        break;
      }

      law = 0;
    }

    if (!advanced) {
      return false;
    }
  }
}

} // namespace

int brute_force_reduce_until_size(int max_proof_sequence_length,
                                  int reduction_steps, const Formula &formula,
                                  int max_formula_length, Proof &proof_sequence,
                                  VariableMap &variables_in_use) {

  for (int proof_sequence_length = 1;
       proof_sequence_length <= max_proof_sequence_length;
       ++proof_sequence_length) {
    if (brute_force_reduce_of_size(proof_sequence_length, reduction_steps,
                                   formula, max_formula_length, proof_sequence,
                                   variables_in_use)) {

      auto print_reduction = [&](const Proof &pseq, int len) {
        std::cout << " Reduction of length " << len << ": [";
        for (int proof_index = 0; proof_index < len; ++proof_index) {
          const auto &step = pseq[proof_index];
          std::cout << LAW_NAMES[step.first] << " at " << step.second;
          if (proof_index + 1 < len) {
            std::cout << ", ";
          }
        }
        std::cout << "]\n";
      };

      print_reduction(proof_sequence, proof_sequence_length);

      return proof_sequence_length;
    }
  }

  std::cout << " No reduction found\n";
  return -1;
}

} // namespace fe
