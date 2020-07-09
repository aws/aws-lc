set(_doc "Command line tool to manage a series of patches")

find_program(QUILT_EXECUTABLE
    NAMES quilt
    DOC ${_doc}
    )

if(NOT QUILT_EXECUTABLE)
    message(FATAL_ERROR "Unable to find quilt executable")
endif()

# Display list of patches being applied
execute_process(
    COMMAND ${QUILT_EXECUTABLE} series -v
    )

# Use quilt to apply patch series
#   -a : apply all patches in the series file
#   -v : verbose operation
#   --leave-rejects : leave around the reject files produced by the patch when unsuccessful
execute_process(
    COMMAND ${QUILT_EXECUTABLE} push -av --leave-rejects
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
    RESULT_VARIABLE PUSH_RESULT
    )

# Fail if unable to apply all patches successfully
if(PUSH_RESULT EQUAL 1)
    message(FATAL_ERROR "Unable to apply patches, exiting.")
endif()
