#------------------------------------------------------------------------------------
# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#------------------------------------------------------------------------------------

cmake_minimum_required(VERSION 3.15)
project(benchmark_ec_p256 C)

set(CMAKE_C_STANDARD 99)

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# Currently, this option only takes effect on ARMv8 (AArch64)
if(COUNTER_REGISTER)
    add_definitions(-DCOUNTER_REGISTER)
endif(COUNTER_REGISTER)

add_executable(${PROJECT_NAME}_awslc "")
add_executable(${PROJECT_NAME}_ossl "")
if(OPENSSL102_LIB)
    add_definitions(-DOPENSSL102)
    add_executable(${PROJECT_NAME}_ossl102 "")
endif()

add_subdirectory(src)
