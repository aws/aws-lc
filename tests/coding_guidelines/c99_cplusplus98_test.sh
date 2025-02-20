#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

# This test is aimed to run with GCC 6 and above on x86-64 architectures.

INCLUDE_DIR="./include"

INCLUDE_FILES=`ls $INCLUDE_DIR/openssl/*.h | grep -v $INCLUDE_DIR/openssl/arm_arch.h`

# - This compilation line gets no source files as its input (it uses the -c flag).
#   Instead it uses the force include flag (-include) to include all of headers
#   except for arm_arch.h, which cannot run on x86-64 architectures.
# - The -Wpedantic flag ensures that the compiler will fault if a non C99 line 
#   exists in the code.
# - The -fsyntax-only tells the compiler to check the syntax without producing 
#   any outputs.
#
# This test has some known limitations:
# "Some users try to use -Wpedantic to check programs for strict ISO C
# conformance. They soon find that it does not do quite what they want: it finds
# some non-ISO practices, but not all — only those for which ISO C requires a
# diagnostic, and some others for which diagnostics have been added."
# https://gcc.gnu.org/onlinedocs/gcc/Warning-Options.html
${CC} -std=c99 -c -I${INCLUDE_DIR} $(echo ${INCLUDE_FILES} | sed 's/[^ ]* */-include &/g') -Wpedantic -fsyntax-only -Werror ./tests/compiler_features_tests/builtin_swap_check.c

# AWS C SDKs conforms to C99. They set `C_STANDARD 99` which will set the
# flag `-std=gnu99`
# https://github.com/awslabs/aws-c-common/blob/main/cmake/AwsCFlags.cmake
# https://github.com/aws/aws-encryption-sdk-c/blob/master/cmake/AwsCryptosdkCFlags.cmake
# https://cmake.org/cmake/help/latest/prop_tgt/C_STANDARD.html
#
# the c99 and gnu99 modes are different, so let's test both.
${CC} -std=gnu99 -c -I${INCLUDE_DIR} $(echo ${INCLUDE_FILES} | sed 's/[^ ]* */-include &/g') -Wpedantic -fsyntax-only -Werror ./tests/compiler_features_tests/builtin_swap_check.c

# Our SSL headers use C++, but older compilers do not have the C++11 flag enabled by
# default. Not all consuming applications that use older compilers have enabled the
# C++11 feature flag. To ensure a smoother integration process for migrating
# applications, we should ensure that the default settings of older C++ compilers
# work with our header files.
${CXX} -std=c++98 -c -I${INCLUDE_DIR} $(echo ${INCLUDE_FILES} | sed 's/[^ ]* */-include &/g') -Wpedantic -fsyntax-only -Werror ./tests/compiler_features_tests/builtin_swap_check.c
${CXX} -std=gnu++98 -c -I${INCLUDE_DIR} $(echo ${INCLUDE_FILES} | sed 's/[^ ]* */-include &/g') -Wpedantic -fsyntax-only -Werror ./tests/compiler_features_tests/builtin_swap_check.c
