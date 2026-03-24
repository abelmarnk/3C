#pragma once
#include "formula_enumerator/formula.hpp"
#include "formula_enumerator/rewriter.hpp"
#include <utility>
#include <vector>

namespace fe {

using ProofStep = std::pair<int, int>; // <Law, Index>
using Proof = std::vector<ProofStep>;

bool is_proof_sequence(const Formula &, int, const Proof &, int, VariableMap &);

int brute_force_proof_until_size(int, int, const Formula &, int, Proof &,
                                 VariableMap &);

int brute_force_reduce_until_size(int, int, const Formula &, int, Proof &,
                                  VariableMap &);

} // namespace fe
