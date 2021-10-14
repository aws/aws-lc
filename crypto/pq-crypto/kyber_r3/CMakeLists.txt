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

set(CFLAGS ${CFLAGS} -Wall -Wextra -Wpedantic -Wmissing-prototypes -Wredundant-decls -Wshadow -Wpointer-arith -mavx2 -mbmi2 -mpopcnt -maes -march=native -mtune=native -O3 -fomit-frame-pointer)

file(GLOB KYBER_R3_SRCS 
"avx2/keccak4x/KeccakP-1600-times4-SIMD256.c"
                       "avx2/keccak4x/KeccakP-1600-unrolling.macros"
                       "avx2/aes256ctr.c"
                       "avx2/basemul.S"
                       "avx2/cbd.c"
                       "avx2/consts.c"
                       "avx2/fips202.c"
                       "avx2/fips202x4.c"
                       "avx2/symmetric-shake.c"
                       "avx2/fq.S"
                       "avx2/fq.inc"
                       "avx2/indcpa.c"
                       "avx2/ntt.S"
                       "avx2/invntt.S"
                       "avx2/kem.c"
                       "avx2/poly.c"
                       "avx2/polyvec.c"
                       "avx2/randombytes.c"
                       "avx2/rejsample.c"
                       "avx2/shuffle.S"
                       "avx2/shuffle.inc"
                       "avx2/verify.c")

add_library(kyber_r3 OBJECT ${KYBER_R3_SRCS})


message(STATUS "${KYBER_R3_SRCS}")

# Setting some necessary flags for KYBER (see config.h)
# Only the generic implementation of KYBER is imported for now.
target_compile_options(kyber_r3 PRIVATE -mavx2 -D_X86_)

if(${CMAKE_SYSTEM_PROCESSOR} MATCHES "x86_64|amd64|AMD64")
  # If ARCH is originally detected as 64-bit, perform an additional check
  # to determine whether to build as 32-bit or 64-bit. This happens in some
  # cases such as when building in Docker, where the host-level architecture is 64-bit
  # but the Docker image should result in building for a 32-bit architecture.
  if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    target_compile_options(kyber_r3 PRIVATE ${CFLAGS} -D_AMD64_)
  else()
    target_compile_options(kyber_r3 PRIVATE ${CFLAGS} -D_X86_)
  endif()
elseif(${CMAKE_SYSTEM_PROCESSOR} MATCHES "x86|i386|i686")
  target_compile_options(kyber_r3 PRIVATE -D_X86_)
elseif(${CMAKE_SYSTEM_PROCESSOR} MATCHES "arm64.*|ARM64|aarch64")
  target_compile_options(kyber_r3 PRIVATE -D_ARM64_)
elseif(${CMAKE_SYSTEM_PROCESSOR} MATCHES "^arm*")
  target_compile_options(kyber_r3 PRIVATE -D_ARM_)
endif()

if(UNIX)
  target_compile_options(kyber_r3 PRIVATE ${CFLAGS} -D__NIX__)
elseif(WIN32)
  target_compile_options(kyber_r3 PRIVATE ${CFLAGS} -D__WINDOWS__)
endif()

# This is experimental third-party code so we avoid making any unnecessary
# changes to it until the code becomes stable. So we ignore some warnings
# that are not errors.
if(GCC AND CMAKE_C_COMPILER_VERSION VERSION_LESS "5")
  # gcc-4.x reports false-positive warnings that are treated as errors
  # and are enabled by default, i.e., there is no -Wno switch to turn them of
  # individually so we have to turn of all the warnings.
  target_compile_options(kyber_r3 PRIVATE -Wno-error)
elseif(NOT MSVC)
  target_compile_options(kyber_r3 PRIVATE -Wno-missing-braces -Wno-unused-function)
endif()

