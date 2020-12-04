cmake_minimum_required(VERSION 3.15)
project(benchmark_ec_p256 C)

set(CMAKE_C_STANDARD 99)

include_directories(.)

add_executable(${PROJECT_NAME}_awslc "")
add_executable(${PROJECT_NAME}_ossl "")

add_subdirectory(src)
