# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#
# This CMakeLists.txt file defines the rules to build libjitterentropy.a.
# The compilation flags that are used are taken from Makefile in:
#   https://github.com/smuellerDD/jitterentropy-library,
# the same as the source code.

set(JITTER_SOURCES
        ${PROJECT_SOURCE_DIR}/third_party/jitterentropy/src/jitterentropy-base.c
        ${PROJECT_SOURCE_DIR}/third_party/jitterentropy/src/jitterentropy-gcd.c
        ${PROJECT_SOURCE_DIR}/third_party/jitterentropy/src/jitterentropy-health.c
        ${PROJECT_SOURCE_DIR}/third_party/jitterentropy/src/jitterentropy-noise.c
        ${PROJECT_SOURCE_DIR}/third_party/jitterentropy/src/jitterentropy-sha3.c
        ${PROJECT_SOURCE_DIR}/third_party/jitterentropy/src/jitterentropy-timer.c)

include_directories(${PROJECT_SOURCE_DIR}/include)
include_directories(${PROJECT_SOURCE_DIR}/third_party/jitterentropy)

if(WIN32)
    if(MSVC)
        set(JITTER_COMPILE_FLAGS "/Od /W4 /DYNAMICBASE /DAWSLC")
    else()
        set(JITTER_COMPILE_FLAGS "-DAWSLC -fwrapv --param ssp-buffer-size=4 -fvisibility=hidden -Wcast-align -Wmissing-field-initializers -Wshadow -Wswitch-enum -Wextra -Wall -pedantic -O0 -fwrapv -Wconversion")
    endif()
else()
    set(CMAKE_POSITION_INDEPENDENT_CODE true)
    set(JITTER_COMPILE_FLAGS "-DAWSLC -fwrapv --param ssp-buffer-size=4 -fvisibility=hidden -Wcast-align -Wmissing-field-initializers -Wshadow -Wswitch-enum -Wextra -Wall -pedantic -O0 -fwrapv")
    if ((NOT GCC) OR (GCC AND CMAKE_C_COMPILER_VERSION VERSION_GREATER "4.3"))
        # -Wconversion was changed from GCC version 4.3. Prior it was meant as
        # an aid in translating code from old C to modern C. It was not meant
        # to help detect troublesome implicit conversions.
        # https://gcc.gnu.org/wiki/NewWconversion.
        set(JITTER_COMPILE_FLAGS "${JITTER_COMPILE_FLAGS} -Wconversion")
    endif()

    if(BORINGSSL_PREFIX)
        set(JITTER_COMPILE_FLAGS "${JITTER_COMPILE_FLAGS} --include=${PROJECT_BINARY_DIR}/symbol_prefix_include/openssl/boringssl_prefix_symbols.h")
    endif()
endif()

set_source_files_properties(${JITTER_SOURCES} PROPERTIES COMPILE_FLAGS "${JITTER_COMPILE_FLAGS}")
add_library(jitterentropy OBJECT ${JITTER_SOURCES})
add_dependencies(jitterentropy boringssl_prefix_symbols)
target_include_directories(jitterentropy BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
