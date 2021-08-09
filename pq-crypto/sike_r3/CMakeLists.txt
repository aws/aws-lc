cmake_minimum_required (VERSION 3.0)

# set compiler
#if(CMAKE_C_COMPILER_ID MATCHES "Clang")
#    set(CLANG 1)
#elseif(CMAKE_C_COMPILER_ID MATCHES "GNU")
#    set(GCC 1)
#endif()

# get all header and source files
file(GLOB PQ_HEADERS "*.h")
file(GLOB PQ_SRC "*.c")

# compile
add_library(sike_lib ${PQ_HEADERS} ${PQ_SRC})