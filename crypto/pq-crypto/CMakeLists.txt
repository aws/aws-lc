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

include_directories(../../include)

add_subdirectory(sike_r3)



if(${CMAKE_SYSTEM_PROCESSOR} MATCHES "x86_64|amd64|AMD64")
  # If ARCH is originally detected as 64-bit, perform an additional check
  # to determine whether to build as 32-bit or 64-bit. This happens in some
  # cases such as when building in Docker, where the host-level architecture is 64-bit
  # but the Docker image should result in building for a 32-bit architecture.
  if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    add_subdirectory(kyber_r3/avx2)
  else()
add_subdirectory(kyber_r3)
  endif()
elseif(${CMAKE_SYSTEM_PROCESSOR} MATCHES "x86|i386|i686")
add_subdirectory(kyber_r3)
elseif(${CMAKE_SYSTEM_PROCESSOR} MATCHES "arm64.*|ARM64|aarch64")
add_subdirectory(kyber_r3)
elseif(${CMAKE_SYSTEM_PROCESSOR} MATCHES "^arm*")
add_subdirectory(kyber_r3)
endif()


add_library(pq_crypto "pq_kem.c"
                      $<TARGET_OBJECTS:sike_r3> $<TARGET_OBJECTS:kyber_r3>)

install(TARGETS pq_crypto
        EXPORT crypto-targets
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
)


if(BUILD_TESTING)
  add_executable(pq_crypto_test pq_kem_test.cc $<TARGET_OBJECTS:boringssl_gtest_main>)
  target_link_libraries(pq_crypto_test test_support_lib boringssl_gtest crypto pq_crypto)
  if(WIN32)
    target_link_libraries(pq_crypto_test ws2_32)
  endif()
  add_dependencies(all_tests pq_crypto_test)
endif ()
