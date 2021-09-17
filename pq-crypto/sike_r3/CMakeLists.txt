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

file(GLOB SIKE_R3_SRCS "P434/P434.c"
                       "P434/generic/fp_generic.c"
                       "random/random.c"
                       "sha3/fips202.c")

add_library(sike_r3 OBJECT ${SIKE_R3_SRCS})

# Setting some necessary flags for SIKE (see config.h)
# Only the generic implementation of SIKE is imported for now.
target_compile_options(sike_r3 PRIVATE -D_GENERIC_)

if("${ARCH}" STREQUAL "x86_64")
  target_compile_options(sike_r3 PRIVATE -D_AMD64_)
elseif("${ARCH}" STREQUAL "x86")
  target_compile_options(sike_r3 PRIVATE -D_X86_)
elseif("${ARCH}" STREQUAL "aarch64")
  target_compile_options(sike_r3 PRIVATE -D_ARM64_)
elseif("${ARCH}" STREQUAL "arm")
  target_compile_options(sike_r3 PRIVATE -D_ARM_)
endif()

if(UNIX)
  target_compile_options(sike_r3 PRIVATE -D__NIX__)
elseif(WIN32)
  target_compile_options(sike_r3 PRIVATE -D__WINDOWS__)
endif()

# This is experimental third-party code so we avoid making any unnecessary
# changes to it until the code becomes stable. So we ignore some warnings
# that are not errors.
target_compile_options(sike_r3 PRIVATE -Wno-missing-braces -Wno-unused-function)

