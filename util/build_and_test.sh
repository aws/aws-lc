#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -ex

BASE_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}/" )/.." &> /dev/null && pwd )

AWS_LC_BUILD="${BASE_DIR}/build"

DEFAULT_CMAKE_FLAGS=("-DCMAKE_BUILD_TYPE=Debug" "-GNinja")

BUILD_TARGET="all_tests"
RUN_TARGET="run_tests"
BUILD_ONLY=false
SANITIZER=""
TEST_BINARY=""
CMAKE_ARGS=()

# Ensures LLVM_PROJECT_HOME is set, cloning if necessary.
# MSAN and TSAN require an MSAN-instrumented libc++ (USE_CUSTOM_LIBCXX), which
# is built from LLVM source. If LLVM_PROJECT_HOME is not already set, this
# function performs a minimal sparse clone of the LLVM project (libcxx and
# libcxxabi only) and caches it under /tmp for subsequent runs.
setup_llvm_project() {
  if [[ -n "${LLVM_PROJECT_HOME:-}" ]]; then
    echo "Using LLVM_PROJECT_HOME=${LLVM_PROJECT_HOME}"
    return
  fi

  local llvm_cache_dir="/tmp/aws-lc-llvm-project"
  if [[ -d "${llvm_cache_dir}/libcxx" && -d "${llvm_cache_dir}/libcxxabi" ]]; then
    echo "Using cached LLVM project at ${llvm_cache_dir}"
  else
    echo "LLVM_PROJECT_HOME not set. Cloning llvm-project to ${llvm_cache_dir}..."
    rm -rf "${llvm_cache_dir}"
    git clone https://github.com/llvm/llvm-project.git \
      --branch llvmorg-19.1.7 --depth 1 \
      --filter=blob:none --sparse \
      "${llvm_cache_dir}"
    pushd "${llvm_cache_dir}"
    git sparse-checkout set libcxx libcxxabi
    popd
  fi
  export LLVM_PROJECT_HOME="${llvm_cache_dir}"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --build-only)
      BUILD_ONLY=true
      shift
      ;;
    --build-target)
      BUILD_TARGET="$2"
      shift 2
      ;;
    --run-target)
      RUN_TARGET="$2"
      shift 2
      ;;
    --sanitizer)
      SANITIZER="$2"
      shift 2
      ;;
    --test)
      TEST_BINARY="$2"
      BUILD_TARGET="$2"
      shift 2
      ;;
    *)
      # Everything else gets passed to CMake
      CMAKE_ARGS+=("$1")
      shift
      ;;
  esac
done

# Handle sanitizer configuration
if [[ -n "${SANITIZER}" ]]; then
  # Sanitizer builds require a clean build directory to avoid stale artifacts
  # from a different configuration (e.g., switching from ASAN to MSAN).
  rm -rf "${AWS_LC_BUILD}"
  export AWS_LC_GO_TEST_TIMEOUT="${AWS_LC_GO_TEST_TIMEOUT:-90m}"

  # All sanitizers require Clang.
  export CC=${CC:-clang}
  export CXX=${CXX:-clang++}

  case "${SANITIZER}" in
    asan)
      CMAKE_ARGS+=("-DASAN=1")
      ;;
    msan)
      CMAKE_ARGS+=("-DMSAN=1" "-DUSE_CUSTOM_LIBCXX=1")
      setup_llvm_project
      CMAKE_ARGS+=("-DLLVM_PROJECT_HOME=${LLVM_PROJECT_HOME}")
      ;;
    tsan)
      CMAKE_ARGS+=("-DTSAN=1" "-DUSE_CUSTOM_LIBCXX=1")
      setup_llvm_project
      CMAKE_ARGS+=("-DLLVM_PROJECT_HOME=${LLVM_PROJECT_HOME}")
      ;;
    ubsan)
      CMAKE_ARGS+=("-DUBSAN=1")
      ;;
    cfi)
      CMAKE_ARGS+=("-DCFI=1")
      ;;
    *)
      echo "Error: Unknown sanitizer '${SANITIZER}'. Supported: asan, msan, tsan, ubsan, cfi"
      exit 1
      ;;
  esac
fi

mkdir -p "${AWS_LC_BUILD}"

cmake "${BASE_DIR}" -B "${AWS_LC_BUILD}" "${DEFAULT_CMAKE_FLAGS[@]}" "${CMAKE_ARGS[@]}"

cmake --build "${AWS_LC_BUILD}" -j --target ${BUILD_TARGET}

if [[ -n "${TEST_BINARY}" ]]; then
  # --test was specified: find and run the test binary directly instead of
  # going through the heavyweight run_tests CMake target.
  TEST_PATH=$(find "${AWS_LC_BUILD}" -name "${TEST_BINARY}" -type f -executable | head -1)
  if [[ -z "${TEST_PATH}" ]]; then
    echo "Error: Could not find test binary '${TEST_BINARY}' in ${AWS_LC_BUILD}"
    exit 1
  fi
  "${TEST_PATH}"
elif [ "$BUILD_ONLY" = false ]; then
  # Default: run via the CMake run_tests target (Go tests + SSL runner + unit tests).
  cmake --build "${AWS_LC_BUILD}" --target ${RUN_TARGET}
fi
