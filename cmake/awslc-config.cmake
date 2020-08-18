# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
#
# Inspired by s2n https://github.com/awslabs/s2n/tree/master/cmake/modules
#
# - Try to find LibCrypto include dirs and libraries.
#
# Normally, AWS-LC built artifacts includes three dirs:
#    bin/
#    include/
#    lib/
# But, to avoid lib naming collision, a unique folder name can be included:
#    {folder name}/bin/
#    {folder name}include/
#    {folder name}lib/
#
# Usage of this module as follows:
#
# If artifact folder is provided:
#     set(AWSLC_ARTIFACT_FOLDER "xxxx")
#     find_package(AWS-LC HINTS "hints that can find AWSLC built artifacts")
#     target_link_libraries(project-target LibCrypto::Crypto)
# else:
#     find_package(AWS-LC)
#     target_link_libraries(project-target LibCrypto::Crypto)
#
# Variables used by this module, they can change the default behaviour and need
# to be set before calling find_package:
#
# Variables defined by this module:
#
#  LibCrypto_FOUND             System has libcrypto, include and library dirs found
#  LibCrypto_INCLUDE_DIR       The crypto include directories.
#  LibCrypto_LIBRARY           The crypto library, depending on the value of BUILD_SHARED_LIBS.
#  LibCrypto_SHARED_LIBRARY    The path to libcrypto.so
#  LibCrypto_STATIC_LIBRARY    The path to libcrypto.a

# Define a function to build paths based on CMAKE_PREFIX_PATH and CMAKE_INSTALL_PREFIX.
function(build_paths var_name suffixes)
    set(local_var "")
    foreach (path ${CMAKE_PREFIX_PATH})
        foreach (suffix ${suffixes})
            list(APPEND local_var "${path}/${suffix}")
        endforeach (suffix)
    endforeach (path)
    foreach (path ${CMAKE_INSTALL_PREFIX})
        foreach (suffix ${suffixes})
            list(APPEND local_var "${path}/${suffix}")
        endforeach (suffix)
    endforeach (path)
    set(${var_name} "${local_var}" PARENT_SCOPE)
endfunction()

# Define possible suffixes of libcrypto include and lib dirs.
set(AWSLC_INCLUDE_SUFFIXES "")
set(AWSLC_LIB_SUFFIXES "")
if (AWSLC_ARTIFACT_FOLDER)
    list(APPEND AWSLC_INCLUDE_SUFFIXES "${AWSLC_ARTIFACT_FOLDER}/include")
    list(APPEND AWSLC_LIB_SUFFIXES "${AWSLC_ARTIFACT_FOLDER}/lib")
    list(APPEND AWSLC_LIB_SUFFIXES "${AWSLC_ARTIFACT_FOLDER}/lib64")
    list(APPEND AWSLC_LIB_SUFFIXES "${AWSLC_ARTIFACT_FOLDER}")
    list(APPEND AWSLC_LIB_SUFFIXES "build/${AWSLC_ARTIFACT_FOLDER}")
else ()
    list(APPEND AWSLC_INCLUDE_SUFFIXES "include")
    list(APPEND AWSLC_LIB_SUFFIXES "lib")
    list(APPEND AWSLC_LIB_SUFFIXES "lib64")
    list(APPEND AWSLC_LIB_SUFFIXES "")
    list(APPEND AWSLC_LIB_SUFFIXES "build")
endif ()
message(STATUS "AWSLC_INCLUDE_SUFFIXES: ${AWSLC_INCLUDE_SUFFIXES}")
message(STATUS "AWSLC_LIB_SUFFIXES: ${AWSLC_LIB_SUFFIXES}")

# Define possible paths to AWSLC LibCrypto Include Dir.
set(AWSLC_INCLUDE_PATHS "")
build_paths(AWSLC_INCLUDE_PATHS ${AWSLC_INCLUDE_SUFFIXES})
message(STATUS "AWSLC_INCLUDE_PATHS: ${AWSLC_INCLUDE_PATHS}")

# Define possible paths to AWSLC LibCrypto Lib Dir.
set(AWSLC_LIB_PATHS "")
build_paths(AWSLC_LIB_PATHS ${AWSLC_LIB_SUFFIXES})
message(STATUS "AWSLC_LIB_PATHS: ${AWSLC_LIB_PATHS}")

find_path(LibCrypto_INCLUDE_DIR
        NAMES openssl/crypto.h
        HINTS
        ${AWSLC_INCLUDE_PATHS}
        )

find_library(LibCrypto_SHARED_LIBRARY
        NAMES libcrypto.so libcrypto.dylib
        HINTS
        ${AWSLC_LIB_PATHS}
        )

find_library(LibCrypto_STATIC_LIBRARY
        NAMES libcrypto.a
        HINTS
        ${AWSLC_LIB_PATHS}
        )

if (BUILD_SHARED_LIBS)
    set(LibCrypto_LIBRARY ${LibCrypto_SHARED_LIBRARY})
else()
    set(LibCrypto_LIBRARY ${LibCrypto_STATIC_LIBRARY})
endif()

include(FindPackageHandleStandardArgs)

find_package_handle_standard_args(LibCrypto DEFAULT_MSG
    LibCrypto_LIBRARY
    LibCrypto_INCLUDE_DIR
    )

mark_as_advanced(
    LibCrypto_ROOT_DIR
    LibCrypto_INCLUDE_DIR
    LibCrypto_LIBRARY
    LibCrypto_SHARED_LIBRARY
    LibCrypto_STATIC_LIBRARY
    )

# some versions of cmake have a super esoteric bug around capitalization differences between
# find dependency and find package, just avoid that here by checking and
# setting both.
if(LIBCRYPTO_FOUND OR LibCrypto_FOUND)
    set(LIBCRYPTO_FOUND true)
    set(LibCrypto_FOUND true)

    message(STATUS "LibCrypto Include Dir: ${LibCrypto_INCLUDE_DIR}")
    message(STATUS "LibCrypto Shared Lib:  ${LibCrypto_SHARED_LIBRARY}")
    message(STATUS "LibCrypto Static Lib:  ${LibCrypto_STATIC_LIBRARY}")
    if (NOT TARGET LibCrypto::Crypto AND
        (EXISTS "${LibCrypto_LIBRARY}")
        )
        set(THREADS_PREFER_PTHREAD_FLAG ON)
        find_package(Threads REQUIRED)
        add_library(LibCrypto::Crypto UNKNOWN IMPORTED)
        set_target_properties(LibCrypto::Crypto PROPERTIES
            INTERFACE_INCLUDE_DIRECTORIES "${LibCrypto_INCLUDE_DIR}")
        set_target_properties(LibCrypto::Crypto PROPERTIES
            IMPORTED_LINK_INTERFACE_LANGUAGES "C"
            IMPORTED_LOCATION "${LibCrypto_LIBRARY}")
        add_dependencies(LibCrypto::Crypto Threads::Threads)
    endif()
endif()
