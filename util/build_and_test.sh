#!/usr/bin/env bash

set -ex

BASE_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}/" )/.." &> /dev/null && pwd )

AWS_LC_BUILD="${BASE_DIR}/build"

DEFAULT_CMAKE_FLAGS=("-DCMAKE_BUILD_TYPE=Debug")

RUN_TESTS=true
CMAKE_ARGS=()

for arg in "$@"; do
  if [ "$arg" == "--no-tests" ]; then
    RUN_TESTS=false
  else
    # Everything else gets passed to CMake
    CMAKE_ARGS+=("$arg")
  fi
done

mkdir -p "${AWS_LC_BUILD}"

cmake "${BASE_DIR}" -B "${AWS_LC_BUILD}" "${DEFAULT_CMAKE_FLAGS[@]}" "${CMAKE_ARGS[@]}"

cmake --build "${AWS_LC_BUILD}" -j 4 --target all_tests

# Only run tests if --no-tests was not specified
if [ "$RUN_TESTS" = true ]; then
  cmake --build "${AWS_LC_BUILD}" -j 4 --target run_tests
fi
