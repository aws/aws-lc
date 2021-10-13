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
                       "random/random.c"
                       "sha3/fips202.c")



# Setting some necessary flags for SIKE (see config.h)
# Only the generic implementation of SIKE is imported for now.
# Add the _AMD64_ and _ARM64_ optimizations


set(ARCHITECTURE "_AMD64_")
set(USE_OPT_LEVEL "_FAST_")
set(MULX "-D _MULX_")
set(ADX "-D _ADX_")

if(${CMAKE_SYSTEM_PROCESSOR} MATCHES "x86_64|amd64|AMD64")
  # If ARCH is originally detected as 64-bit, perform an additional check
  # to determine whether to build as 32-bit or 64-bit. This happens in some
  # cases such as when building in Docker, where the host-level architecture is 64-bit
  # but the Docker image should result in building for a 32-bit architecture.
  if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    set(${ARCHITECTURE} "_AMD64_")
    set(USE_OPT_LEVEL "_FAST_")
    set(SIKE_R3_SRCS ${SIKE_R3_SRCS} P434/AMD64/fp_x64.c P434/AMD64/fp_x64_asm.S)
  else()
    set(${ARCHITECTURE} "_X86_")
    set(USE_OPT_LEVEL "_GENERIC_")
    set(SIKE_R3_SRCS ${SIKE_R3_SRCS} P434/generic/fp_generic.c)
  endif()
elseif(${CMAKE_SYSTEM_PROCESSOR} MATCHES "x86|i386|i686")
  set(${ARCHITECTURE} "_X86_")
  set(USE_OPT_LEVEL "_GENERIC_")
  set(SIKE_R3_SRCS ${SIKE_R3_SRCS} P434/generic/fp_generic.c)
elseif(${CMAKE_SYSTEM_PROCESSOR} MATCHES "arm64.*|ARM64|aarch64")
  set(${ARCHITECTURE} "_ARM64_")
  set(USE_OPT_LEVEL "_FAST_")
  set(SIKE_R3_SRCS ${SIKE_R3_SRCS} P434/ARM64/fp_arm64.c P434/AMD64/fp_arm64_asm.S)
elseif(${CMAKE_SYSTEM_PROCESSOR} MATCHES "^arm*")
  set(${ARCHITECTURE} "_ARM_")
  set(USE_OPT_LEVEL "_GENERIC_")
  set(SIKE_R3_SRCS ${SIKE_R3_SRCS} P434/generic/fp_generic.c)
endif()

if(${ARCHITECTURE} STREQUAL _AMD64_)
    if(${USE_OPT_LEVEL} STREQUAL _FAST_)
      set(${MULX} "-D _MULX_")
        if("${USE_MULX}" STREQUAL "FALSE")
            set(${MULX} "")
        else()
            set(${ADX} "-D _ADX_") 
            if("${USE_ADX}" STREQUAL "FALSE")
                set(${ADX} "")
            endif()
        endif()
    endif()
endif()




add_library(sike_r3 OBJECT ${SIKE_R3_SRCS})

message(STATUS "${SIKE_R3_SRCS}")


if(UNIX)
  target_compile_options(sike_r3 PRIVATE -D ${ARCHITECTURE} -D__NIX__ -D${USE_OPT_LEVEL} ${MULX} ${ADX})
elseif(WIN32)
  target_compile_options(sike_r3 PRIVATE -D__WINDOWS__)
endif()




# This is experimental third-party code so we avoid making any unnecessary
# changes to it until the code becomes stable. So we ignore some warnings
# that are not errors.
if(GCC AND CMAKE_C_COMPILER_VERSION VERSION_LESS "5")
  # gcc-4.x reports false-positive warnings that are treated as errors
  # and are enabled by default, i.e., there is no -Wno switch to turn them of
  # individually so we have to turn of all the warnings.
  target_compile_options(sike_r3 PRIVATE -Wno-error)
elseif(NOT MSVC)
  target_compile_options(sike_r3 PRIVATE -Wno-missing-braces -Wno-unused-function)
endif()

