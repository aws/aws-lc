cmake_minimum_required(VERSION 2.8.12)

project(AWSLC NONE)

include(cmake/apply-quilt-patches.cmake)
add_subdirectory(third_party/boringssl)
