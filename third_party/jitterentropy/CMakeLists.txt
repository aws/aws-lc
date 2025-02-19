# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#
# This CMakeLists.txt file defines the rules to build libjitterentropy.a.
# The compilation flags that are used are taken from Makefile in:
#   https://github.com/smuellerDD/jitterentropy-library,
# the same as the source code.

set(JITTER_SOURCES
        ${AWSLC_SOURCE_DIR}/third_party/jitterentropy/jitterentropy-base.c
        ${AWSLC_SOURCE_DIR}/third_party/jitterentropy/jitterentropy-gcd.c
        ${AWSLC_SOURCE_DIR}/third_party/jitterentropy/jitterentropy-health.c
        ${AWSLC_SOURCE_DIR}/third_party/jitterentropy/jitterentropy-noise.c
        ${AWSLC_SOURCE_DIR}/third_party/jitterentropy/jitterentropy-sha3.c
        ${AWSLC_SOURCE_DIR}/third_party/jitterentropy/jitterentropy-timer.c)

include_directories(${AWSLC_SOURCE_DIR}/include)

if(MSVC)
    set(JITTER_COMPILE_FLAGS "/Od /W4 /DYNAMICBASE /DAWSLC")
else()
    set(JITTER_COMPILE_FLAGS "-DAWSLC -fwrapv --param ssp-buffer-size=4 -fvisibility=hidden -fPIE -Wcast-align -Wmissing-field-initializers -Wshadow -Wswitch-enum -Wextra -Wall -pedantic -fPIC -O0 -fwrapv -Wconversion")
endif()

set_source_files_properties(${JITTER_SOURCES} PROPERTIES COMPILE_FLAGS ${JITTER_COMPILE_FLAGS})
add_library(jitterentropy OBJECT ${JITTER_SOURCES})
add_dependencies(jitterentropy boringssl_prefix_symbols)
target_include_directories(jitterentropy BEFORE PRIVATE ${PROJECT_BINARY_DIR}/symbol_prefix_include)
