# CompilerWrapper.cmake
#
# CMake module for handling compiler flag conflicts, particularly the -S/-c conflict
# in newer Clang versions when generating assembly output.
#
# This module dynamically generates wrapper scripts with hardcoded compiler paths,
# eliminating the need for complex compiler discovery logic.
#
# Usage:
#   include(CompilerWrapper)
#   setup_compiler_wrapper()
#   use_compiler_wrapper_for_target(my_target)

cmake_minimum_required(VERSION 3.10)

# Check if we need the compiler wrapper based on compiler version
function(compiler_wrapper_needed result_var)
  set(${result_var} FALSE PARENT_SCOPE)

  # Check C compiler
  if(CMAKE_C_COMPILER_ID MATCHES "Clang" OR CMAKE_C_COMPILER MATCHES "clang")
    if(CMAKE_C_COMPILER_VERSION VERSION_GREATER "19.99.99")
      set(${result_var} TRUE PARENT_SCOPE)
      return()
    endif()
  endif()

  # Allow manual override via CMake variable
  if(FORCE_COMPILER_WRAPPER)
    set(${result_var} TRUE PARENT_SCOPE)
  endif()
endfunction()

# Generate wrapper scripts with hardcoded compiler paths
function(generate_compiler_wrapper)
  # Get current timestamp for generated file header
  string(TIMESTAMP CURRENT_TIMESTAMP UTC)

  # Set output directory for generated wrappers
  set(WRAPPER_OUTPUT_DIR "${CMAKE_BINARY_DIR}/compiler_wrapper")
  file(MAKE_DIRECTORY "${WRAPPER_OUTPUT_DIR}")

  # Generate shell script wrapper (Unix/Linux/macOS)
  set(SHELL_TEMPLATE "${CMAKE_SOURCE_DIR}/util/compiler_wrapper/compiler_wrapper_template.sh.in")
  set(SHELL_OUTPUT "${WRAPPER_OUTPUT_DIR}/compiler_wrapper.sh")

  if(EXISTS "${SHELL_TEMPLATE}")
    # Output file retains permissions of source file.
    configure_file(
            "${SHELL_TEMPLATE}"
            "${SHELL_OUTPUT}"
            @ONLY
        )

    set(COMPILER_WRAPPER_SHELL "${SHELL_OUTPUT}" PARENT_SCOPE)
    message(STATUS "Generated shell wrapper: ${SHELL_OUTPUT}")
  else()
    message(WARNING "Shell wrapper template not found: ${SHELL_TEMPLATE}")
  endif()

  # Generate batch file wrapper (Windows)
  set(BAT_TEMPLATE "${CMAKE_SOURCE_DIR}/util/compiler_wrapper/compiler_wrapper_template.bat.in")
  set(BAT_OUTPUT "${WRAPPER_OUTPUT_DIR}/compiler_wrapper.bat")

  if(EXISTS "${BAT_TEMPLATE}")
    configure_file(
            "${BAT_TEMPLATE}"
            "${BAT_OUTPUT}"
            @ONLY
        )

    set(COMPILER_WRAPPER_BAT "${BAT_OUTPUT}" PARENT_SCOPE)
    message(STATUS "Generated batch wrapper: ${BAT_OUTPUT}")
  else()
    message(WARNING "Batch wrapper template not found: ${BAT_TEMPLATE}")
  endif()
endfunction()

# Get the appropriate wrapper script for the current platform
function(get_platform_wrapper result_var)
  if(WIN32 AND COMPILER_WRAPPER_BAT
           AND EXISTS "${COMPILER_WRAPPER_BAT}")
    set(${result_var} "${COMPILER_WRAPPER_BAT}" PARENT_SCOPE)
  elseif(COMPILER_WRAPPER_SHELL AND EXISTS "${COMPILER_WRAPPER_SHELL}")
    set(${result_var} "${COMPILER_WRAPPER_SHELL}" PARENT_SCOPE)
  else()
    set(${result_var} "" PARENT_SCOPE)
  endif()
endfunction()

# Set up the compiler wrapper system
function(setup_compiler_wrapper)
  # Check if we need the wrapper
  compiler_wrapper_needed(NEED_WRAPPER)
  if(NOT NEED_WRAPPER)
    message(STATUS "Compiler wrapper not needed for current compiler version")
    set(COMPILER_WRAPPER_AVAILABLE FALSE CACHE INTERNAL "Whether compiler wrapper is available")
    return()
  endif()

  # Determine the compiler to wrap
  set(REAL_COMPILER "${CMAKE_C_COMPILER}")
  if(NOT REAL_COMPILER)
    message(FATAL_ERROR "CMAKE_C_COMPILER is not set, cannot generate compiler wrapper")
  endif()

  # Convert to absolute path if needed
  if(NOT IS_ABSOLUTE "${REAL_COMPILER}")
    find_program(REAL_COMPILER_ABS "${REAL_COMPILER}")
    if(REAL_COMPILER_ABS)
      set(REAL_COMPILER "${REAL_COMPILER_ABS}")
    else()
      message(WARNING "Could not find absolute path for compiler: ${REAL_COMPILER}")
    endif()
  endif()

  # Verify compiler exists
  if(NOT EXISTS "${REAL_COMPILER}")
    message(FATAL_ERROR "Compiler not found: ${REAL_COMPILER}")
  endif()

  message(STATUS "Generating compiler wrapper for: ${REAL_COMPILER}")

  # Generate the wrapper scripts
  generate_compiler_wrapper()
  # Get the platform-appropriate wrapper
  get_platform_wrapper(WRAPPER_SCRIPT)

  if(NOT WRAPPER_SCRIPT OR NOT EXISTS "${WRAPPER_SCRIPT}")
    message(FATAL_ERROR "Failed to generate compiler wrapper script")
  endif()

  # Store wrapper information in cache for use by other functions
  set(COMPILER_WRAPPER_SCRIPT "${WRAPPER_SCRIPT}" CACHE INTERNAL "Path to generated compiler wrapper script")
  set(COMPILER_WRAPPER_REAL_COMPILER "${REAL_COMPILER}" CACHE INTERNAL "Real compiler being wrapped")
  set(COMPILER_WRAPPER_AVAILABLE TRUE CACHE INTERNAL "Whether compiler wrapper is available")

  message(STATUS "Compiler wrapper ready: ${WRAPPER_SCRIPT}")
endfunction()

# Apply the compiler wrapper to a specific target
function(use_compiler_wrapper_for_target target_name)
  # Check that wrapper is available
  if(NOT COMPILER_WRAPPER_AVAILABLE)
    message(STATUS "Compiler wrapper not available for target ${target_name}")
    return()
  endif()

  # Check that target exists
  if(NOT TARGET ${target_name})
    message(WARNING "Target ${target_name} does not exist, cannot apply compiler wrapper")
    return()
  endif()

  # Set the compiler launcher to use our wrapper
  set_target_properties(${target_name} PROPERTIES
        C_COMPILER_LAUNCHER "${COMPILER_WRAPPER_SCRIPT}"
    )

  message(STATUS "Applied compiler wrapper to target: ${target_name}")
endfunction()
