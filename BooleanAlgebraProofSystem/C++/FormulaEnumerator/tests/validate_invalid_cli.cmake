execute_process(
    COMMAND "${PROGRAM}" --mode reduction --target tautology
    RESULT_VARIABLE result
    OUTPUT_VARIABLE stdout_text
    ERROR_VARIABLE stderr_text
)

set(combined_output "${stdout_text}${stderr_text}")

if(result EQUAL 0)
    message(FATAL_ERROR "Expected invalid CLI invocation to fail, but it succeeded.")
endif()

if(NOT combined_output MATCHES "--target and --proof-limit are only valid with --mode target\\.")
    message(FATAL_ERROR "Expected validation error message was not found.\n${combined_output}")
endif()
