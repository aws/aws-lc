#------------------------------------------------------------------------------------
# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC
#------------------------------------------------------------------------------------

# Build ec_benchmark with AWS-LC
#-------------------------------
# Add the source files to the target that builds with AWS-LC
target_sources(${PROJECT_NAME}_awslc
    PRIVATE
        benchmark.c
        benchmark.h
        benchmark_ecdh.c
        benchmark_ecdsa.c
        main.c
        )

# Find AWS-LC libcrypto.a
# For more HINTS to find the library and include files see
# aws-lc/cmake/awslc-config.cmake
find_library(AWSLC_LIBCRYPTO crypto
        HINTS ${CMAKE_SOURCE_DIR}/../aws-lc/build/crypto
        )

# Add libcrypto.a as a link library to the target
target_link_libraries(${PROJECT_NAME}_awslc PUBLIC ${AWSLC_LIBCRYPTO})

# Add pthread as a link library using code from "aws-lc/crypto/CMakeLists.txt"
if(NOT WIN32 AND NOT ANDROID)
  target_link_libraries(${PROJECT_NAME}_awslc PUBLIC pthread)
endif()

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fvisibility=hidden -Wall -Wextra -Werror -Wpedantic")

# Include directories, adding AWS-LC include
target_include_directories(${PROJECT_NAME}_awslc
        PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
        ${CMAKE_SOURCE_DIR}/../aws-lc/include
        )

# Add -DAWSLC_BENCHMARK as a compilation flag
target_compile_definitions(${PROJECT_NAME}_awslc PUBLIC AWSLC_BENCHMARK)

# Build ec_benchmark with OpenSSL
#--------------------------------
# Add the source files to the target that builds with OpenSSL
target_sources(${PROJECT_NAME}_ossl
        PRIVATE
        benchmark.c
        benchmark.h
        benchmark_ecdh.c
        benchmark_ecdsa.c
        main.c
        )

# Find OpenSSL libcrypto.a
find_library(OPENSSL_LIBCRYPTO crypto
        HINTS ${CMAKE_SOURCE_DIR}/../openssl
        )

# Add libcrypto.a as a link library to the target
target_link_libraries(${PROJECT_NAME}_ossl PUBLIC ${OPENSSL_LIBCRYPTO})

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fvisibility=hidden -Wall -Wextra -Werror -Wpedantic")

# Include directories, adding AWS-LC include
target_include_directories(${PROJECT_NAME}_ossl
        PUBLIC
        ${CMAKE_CURRENT_LIST_DIR}
        ${CMAKE_SOURCE_DIR}/../openssl/include
        )

# Build ec_benchmark with OpenSSL 1.0.2, if defined
#--------------------------------------------------
# Add the source files to the target that builds with OpenSSL 1.0.2
if(OPENSSL102_LIB)
    target_sources(${PROJECT_NAME}_ossl102
            PRIVATE
            benchmark.c
            benchmark.h
            benchmark_ecdh.c
            benchmark_ecdsa.c
            main.c
            )

    # Find AWS-LC libcrypto.a
    find_library(OPENSSL102_LIBCRYPTO crypto
            HINTS ${CMAKE_SOURCE_DIR}/../openssl102/openssl
            )

    # Add libcrypto.a as a link library to the target
    target_link_libraries(${PROJECT_NAME}_ossl102 PUBLIC ${OPENSSL102_LIBCRYPTO})

    if (UNIX)
       target_link_libraries(${PROJECT_NAME}_ossl102 PUBLIC dl)
    endif(UNIX)

    # Include directories, adding AWS-LC include
    target_include_directories(${PROJECT_NAME}_ossl102
            PUBLIC
            ${CMAKE_CURRENT_LIST_DIR}
            ${CMAKE_SOURCE_DIR}/../openssl102/openssl/include
            )
endif(OPENSSL102_LIB)
