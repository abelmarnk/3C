cmake_minimum_required(VERSION 3.16)
project(FormulaEnumeratorCpp LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_library(formula_enumerator_lib
    src/formula.cpp
    src/evaluator.cpp
    src/rewriter.cpp
    src/proof_search.cpp
    src/enumerator.cpp
)

target_include_directories(formula_enumerator_lib PUBLIC include)

add_executable(formula_enumerator
    src/main.cpp
)
target_link_libraries(formula_enumerator PRIVATE formula_enumerator_lib)

enable_testing()

add_executable(formula_enumerator_tests
    tests/formula_enumerator_tests.cpp
)
target_link_libraries(formula_enumerator_tests PRIVATE formula_enumerator_lib)

if (CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    target_compile_options(formula_enumerator_lib PRIVATE -Wall -Wextra -Wpedantic)
    target_compile_options(formula_enumerator PRIVATE -Wall -Wextra -Wpedantic)
    target_compile_options(formula_enumerator_tests PRIVATE -Wall -Wextra -Wpedantic)
endif()

add_test(NAME formula_enumerator_unit COMMAND formula_enumerator_tests)

add_test(NAME formula_enumerator_cli_default COMMAND formula_enumerator)
set_tests_properties(
    formula_enumerator_cli_default
    PROPERTIES PASS_REGULAR_EXPRESSION
    "There are 25 Boolean formulas with 3 symbols and with valid syntax and variable labeling\\."
)

add_test(NAME formula_enumerator_cli_contradiction
    COMMAND formula_enumerator --target contradiction
)
set_tests_properties(
    formula_enumerator_cli_contradiction
    PROPERTIES PASS_REGULAR_EXPRESSION
    "contradictions"
)

add_test(NAME formula_enumerator_cli_reduction
    COMMAND formula_enumerator --mode reduction
)
set_tests_properties(
    formula_enumerator_cli_reduction
    PROPERTIES PASS_REGULAR_EXPRESSION
    "formulas reducible by at least"
)

add_test(NAME formula_enumerator_cli_invalid
    COMMAND ${CMAKE_COMMAND}
        -DPROGRAM=$<TARGET_FILE:formula_enumerator>
        -P ${CMAKE_CURRENT_SOURCE_DIR}/tests/validate_invalid_cli.cmake
)
