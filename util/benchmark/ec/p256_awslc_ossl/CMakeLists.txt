cmake_minimum_required(VERSION 3.15)
project(benchmark_ec_p256 C)

set(CMAKE_C_STANDARD 99)

include_directories(.)

if(UNIX)
    if(CPU_TICKS)
        add_definitions(-DCPU_TICKS)
    endif(CPU_TICKS)
endif(UNIX)

add_executable(${PROJECT_NAME}_awslc "")
add_executable(${PROJECT_NAME}_ossl "")
if(OPENSSL102_LIB)
    add_definitions(-DOPENSSL102)
    add_executable(${PROJECT_NAME}_ossl102 "")
endif()

add_subdirectory(src)
