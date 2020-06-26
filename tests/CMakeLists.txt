# Declare a dummy target to build all unit tests. Test targets should inject
# themselves as dependencies next to the target definition.
add_custom_target(all_tests)

add_subdirectory(unit)
add_subdirectory(../util/fipstools/cavp)
add_subdirectory(../util/fipstools/acvp/modulewrapper)

if(FUZZ)
  add_subdirectory(../fuzz)
endif()

if(NOT ${CMAKE_VERSION} VERSION_LESS "3.2")
  # USES_TERMINAL is only available in CMake 3.2 or later.
  set(MAYBE_USES_TERMINAL USES_TERMINAL)
endif()

add_custom_target(
    run_tests
    COMMAND ${GO_EXECUTABLE} run tests/unit/all_tests.go -build-dir
            ${CMAKE_BINARY_DIR}
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    DEPENDS all_tests
    ${MAYBE_USES_TERMINAL})
