# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# CompilerWrapper.cmake
#
# CMake module for handling the -S/-c flag conflict that arises when CMake
# generates the compile command for the bcm_c_generated_asm target. CMake's
# static library rules always include -c, but we set COMPILE_OPTIONS "-S" to
# produce textual assembly. The wrapper strips -c when -S is present.
#
# This module dynamically generates wrapper scripts with hardcoded compiler paths,
# eliminating the need for complex compiler discovery logic.
#
# Usage:
#   include(CompilerWrapper)
#   setup_compiler_wrapper()
#   use_compiler_wrapper_for_target(my_target)

# The bcm_c_generated_asm target uses COMPILE_OPTIONS "-S" on a normal CMake
# static library, which causes CMake to emit both -S and -c in the same
# command. This is semantically contradictory (-S = emit assembly, -c = emit
# object code). GCC and older Clang versions silently let -S win, but other
# compilers (Clang 20+, Zig) reject or mishandle the conflicting flags. The
# wrapper unconditionally strips -c when -S is present, making the build
# correct for all compilers.
function(compiler_wrapper_needed result_var)
  set(${result_var} TRUE PARENT_SCOPE)
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
