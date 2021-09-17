#
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
#
#  http://aws.amazon.com/apache2.0
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#

cmake_minimum_required (VERSION 2.8.12)

# get all source files
file(GLOB SIKE_R3_SRCS "P434/*.c"
                       "P434/generic/fp_generic.c"
                       "random/random.c"
                       "sha3/fips202.c")

add_library(sike_r3 OBJECT ${SIKE_R3_SRCS})

# TODO(awslc): set the __NIX__ or __WINDOWS__ depending on the OS (see config.h)
target_compile_options(sike_r3 PRIVATE -D__NIX__)

# TODO(awslc): set the correct target option (see config.h)
target_compile_options(sike_r3 PRIVATE -D_AMD64_)

target_compile_options(sike_r3 PRIVATE -Wno-missing-braces -Wno-unused-function)
