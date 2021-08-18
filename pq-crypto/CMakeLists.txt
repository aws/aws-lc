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

cmake_minimum_required (VERSION 3.0)

include_directories(../include)
include_directories(../crypto)

# get all header and source files
file(GLOB PQ_HEADERS "sike_r3/*.h")
file(GLOB PQ_SRC "sike_r3/*.c")

# compile
add_library(pq_lib ${PQ_HEADERS} ${PQ_SRC})
