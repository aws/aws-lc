# For more information about using CMake with Android Studio, read the
# documentation: https://d.android.com/studio/projects/add-native-code.html

# Sets the minimum version of CMake required to build the native library.

cmake_minimum_required(VERSION 3.4.1)

# AWS lib
set(path_to_awslc "${CMAKE_CURRENT_LIST_DIR}/../../../../../../../../")
get_filename_component(path_to_awslc ${path_to_awslc} ABSOLUTE)

list(APPEND CMAKE_MODULE_PATH $<TARGET_FILE:crypto>)
set(ANDROIDTESTRUNNER ON)
add_subdirectory(${path_to_awslc} ${CMAKE_CURRENT_BINARY_DIR}/aws-lc)

# Set up Android Kotlin files.
define_property(GLOBAL PROPERTY ANDROID_TEST_CASES BRIEF_DOCS "Test Cases" FULL_DOCS "Test Cases")
set(ANDROID_TEST_CASES "" CACHE INTERNAL "Test cases valid for this configuration")

# Registers a test case by name
list(APPEND ANDROID_TEST_CASES "crypto_test")
list(APPEND ANDROID_TEST_CASES "urandom_test")
list(APPEND ANDROID_TEST_CASES "ssl_test")

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


