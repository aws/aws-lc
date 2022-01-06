# For more information about using CMake with Android Studio, read the
# documentation: https://d.android.com/studio/projects/add-native-code.html

# Sets the minimum version of CMake required to build the native library.

cmake_minimum_required(VERSION 3.4.1)

# AWS lib
set(path_to_awslc "${CMAKE_CURRENT_LIST_DIR}/../../../../..")
get_filename_component(path_to_awslc ${path_to_awslc} ABSOLUTE)

# This is required in order to append /lib/cmake to each element in CMAKE_PREFIX_PATH
# set(AWS_MODULE_DIR "/${CMAKE_INSTALL_LIBDIR}/cmake")
# string(REPLACE ";" "${AWS_MODULE_DIR};" AWS_MODULE_PATH "${CMAKE_PREFIX_PATH}${AWS_MODULE_DIR}")
# # Append that generated list to the module search path
# list(APPEND CMAKE_MODULE_PATH ${AWS_MODULE_PATH})

list(APPEND CMAKE_MODULE_PATH "${path_to_awslc}/cmake")
# Although we generate our own tests, the generated crypto_test_data object file is needed for the android tests.
set(BUILD_TESTING ON)
set(BUILD_SHARED_LIBS OFF)
set(ANDROIDTESTRUNNER ON)
add_subdirectory(${path_to_awslc} ${CMAKE_CURRENT_BINARY_DIR}/aws-lc)

# gtest needs to be recompiled with the same flags as the current toolchain to avoid unrecognized symbols.
# add_library(android_gtest ${path_to_awslc}/third_party/googletest/src/gtest-all.cc)
# target_include_directories(android_gtest PRIVATE ${path_to_awslc}/third_party/googletest ${path_to_awslc}/third_party/googletest/include)
# include_directories(${path_to_awslc}/third_party/googletest/include)

# we disguise the executable with .so to let Android pack the executable in the apk
# add_executable(android_crypto_test.so

#     ${path_to_awslc}/crypto/abi_self_test.cc
#     ${path_to_awslc}/crypto/crypto_test.cc
#     ${path_to_awslc}/crypto/evp_extra/evp_extra_test.cc
#     ${path_to_awslc}/crypto/test/file_test_gtest.cc

#     $<TARGET_OBJECTS:crypto_test_data>
#     $<TARGET_OBJECTS:boringssl_gtest_main>
# )
# target_include_directories(android_crypto_test.so PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/aws-lc/crypto)
# target_link_libraries(android_crypto_test.so test_support_lib android_gtest crypto)

# add_executable(
#     android_urandom_test.so

#     ${path_to_awslc}/crypto/fipsmodule/rand/urandom_test.cc
# )
# # When using CPU Jitter as the entropy source (only in FIPS build)
# # urandom_test should not be performed so we pass the compilation flag
# # and handle it in urandom_test.cc
# if(JITTER_ENTROPY)
#     target_compile_options(android_urandom_test.so PUBLIC -DJITTER_ENTROPY)
# endif()
# target_link_libraries(android_urandom_test.so test_support_lib android_gtest crypto)


# Set up Android Kotlin files.
define_property(GLOBAL PROPERTY ANDROID_TEST_CASES BRIEF_DOCS "Test Cases" FULL_DOCS "Test Cases")
set(ANDROID_TEST_CASES "" CACHE INTERNAL "Test cases valid for this configuration")

# Registers a test case by name
list(APPEND ANDROID_TEST_CASES "crypto_test")
#list(APPEND ANDROID_TEST_CASES "urandom_test")

# Generate Kotlin test classes
get_filename_component(testrunner_path "../../androidTest/java/software/amazon/aws/crypto/awslcandroidtestrunner" ABSOLUTE)
foreach(name IN LISTS ANDROID_TEST_CASES)
    set(TEST_NAME "${name}")
    configure_file(
        "${testrunner_path}/NativeTest.kt.in"
        "${testrunner_path}/tests/NativeTest_${name}.kt"
        @ONLY
    )
endforeach() 


