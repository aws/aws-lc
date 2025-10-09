#!/usr/bin/env bash

set -ex

BASE_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}/" )/.." &> /dev/null && pwd )

AWS_LC_BUILD="${BASE_DIR}/build"

DEFAULT_CMAKE_FLAGS=("-DCMAKE_BUILD_TYPE=Debug" "-GNinja")

BUILD_ONLY=false
CMAKE_ARGS=()

for arg in "$@"; do
  if [ "$arg" == "--build-only" ]; then
    BUILD_ONLY=true
  else
    # Everything else gets passed to CMake
    CMAKE_ARGS+=("$arg")
  fi
done

mkdir -p "${AWS_LC_BUILD}"

cmake "${BASE_DIR}" -B "${AWS_LC_BUILD}" "${DEFAULT_CMAKE_FLAGS[@]}" "${CMAKE_ARGS[@]}"

cmake --build "${AWS_LC_BUILD}" --target all_tests -j

# Only run tests if --no-tests was not specified
if [ "$BUILD_ONLY" = false ]; then
  cmake --build "${AWS_LC_BUILD}" --target run_tests
fi
