set(_doc "Command line tool to manage a series of patches")

message(STATUS "Finding Quilt and applying patches")
find_program(QUILT_EXECUTABLE
    NAMES quilt
    DOC ${_doc}
    )

if(NOT QUILT_EXECUTABLE)
    message(FATAL_ERROR "Unable to find Quilt")
endif()

# Display list of patches being applied
execute_process(
    COMMAND ${QUILT_EXECUTABLE} series -v
    RESULT_VARIABLE EXIT_CODE
    )
# Check quilt command exit status.
# https://man7.org/linux/man-pages/man1/quilt.1.html#EXIT_STATUS
if(EXIT_CODE EQUAL 1)
    message(FATAL_ERROR "Unable to show patch files, exiting.")
endif()

# Always try to clean up patch stacks before push.
#   -a : Remove all applied patches
#   -v : verbose operation
execute_process(
    COMMAND ${QUILT_EXECUTABLE} pop -av
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
    RESULT_VARIABLE EXIT_CODE
    )
if(EXIT_CODE EQUAL 1)
    message(FATAL_ERROR "Unable to clean up patch stacks, exiting.")
endif()

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
