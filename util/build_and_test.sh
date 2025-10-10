#!/usr/bin/env bash

set -ex

BASE_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}/" )/.." &> /dev/null && pwd )

AWS_LC_BUILD="${BASE_DIR}/build"

DEFAULT_CMAKE_FLAGS=("-DCMAKE_BUILD_TYPE=Debug" "-GNinja")

RUN_TARGET="run_tests"
BUILD_ONLY=false
CMAKE_ARGS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --build-only)
      BUILD_ONLY=true
      shift
      ;;
    --run-target)
      RUN_TARGET="$2"
      shift 2
      ;;
    *)
      # Everything else gets passed to CMake
      CMAKE_ARGS+=("$1")
      shift
      ;;
  esac
done

mkdir -p "${AWS_LC_BUILD}"

cmake "${BASE_DIR}" -B "${AWS_LC_BUILD}" "${DEFAULT_CMAKE_FLAGS[@]}" "${CMAKE_ARGS[@]}"

cmake --build "${AWS_LC_BUILD}" --target all_tests -j

# Only run tests if --build-only was not specified
if [ "$BUILD_ONLY" = false ]; then
  cmake --build "${AWS_LC_BUILD}" --target ${RUN_TARGET}
fi
