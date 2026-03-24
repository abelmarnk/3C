cmake_minimum_required(VERSION 3.16)
project(FormulaEnumeratorCpp LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

add_executable(formula_enumerator
    src/main.cpp
    src/formula.cpp
    src/evaluator.cpp
    src/rewriter.cpp
    src/proof_search.cpp
    src/enumerator.cpp
)

target_include_directories(formula_enumerator PRIVATE include)
if (CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang")
    target_compile_options(formula_enumerator PRIVATE -Wall -Wextra -Wpedantic)
endif()
