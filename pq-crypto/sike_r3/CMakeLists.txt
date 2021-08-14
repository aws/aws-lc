cmake_minimum_required (VERSION 3.0)

include_directories(../../include)
include_directories(../../crypto)


# get all header and source files
file(GLOB PQ_HEADERS "*.h")
file(GLOB PQ_SRC "*.c")

# compile
add_library(sike_lib ${PQ_HEADERS} ${PQ_SRC})
