#pragma once

#include <array>
#include <string_view>

namespace fe {

enum Law : int {
  IDENTITY_OR = 0,
  IDENTITY_AND = 1,
  IDEMPOTENT_OR = 2,
  IDEMPOTENT_AND = 3,
  COMMUTATIVE_NEGATION = 4,
  ASSOCIATIVE_DISTRIBUTIVE_DEMORGAN_DOUBLE_NEGATION = 5,
  COMPLEMENT = 6,
  DOMINATION = 7,
  ABSORPTION_OR = 8,
  ABSORPTION_AND = 9,
  SUBSTITUTION = 10,
  LAW_COUNT = 11
};

inline constexpr std::array<std::string_view, LAW_COUNT> LAW_NAMES = {
    "IDENTITY_OR",          "IDENTITY_AND",
    "IDEMPOTENT_OR",        "IDEMPOTENT_AND",
    "COMMUTATIVE_NEGATION", "ASSOCIATIVE_DISTRIBUTIVE_DEMORGAN_DOUBLE_NEGATION",
    "COMPLEMENT",           "DOMINATION",
    "ABSORPTION_OR",        "ABSORPTION_AND",
    "SUBSTITUTION"};

} // namespace fe
