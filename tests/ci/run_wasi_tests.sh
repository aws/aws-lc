#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# CI script for testing AWS-LC WASI SDK builds
#
# This script builds AWS-LC for WebAssembly using the WASI SDK and runs the
# crypto_test, ssl_test, and urandom_test binaries using a WASI runtime.
#
# Prerequisites:
#   - WASI SDK must be installed (https://github.com/WebAssembly/wasi-sdk)
#   - WASI_SDK_PREFIX environment variable should point to WASI SDK root,
#     or the SDK should be installed at /opt/wasi-sdk
#   - CMake 3.5 or later
#   - Ninja (recommended) or Make
#   - A WASI runtime (wasmtime recommended) for running tests
#
# Environment Variables:
#   WASI_SDK_PREFIX - Path to the WASI SDK (defaults to /opt/wasi-sdk)
#   WASI_RUNTIME    - Path to WASI runtime executable (defaults to wasmtime)
#
# Note: WASI Preview 2 does not currently support pthreads. AWS-LC will be built
# in single-threaded mode. Socket APIs are also not available, so networking
# tests are excluded at compile time.

set -ex

source tests/ci/common_posix_setup.sh

# Default WASI SDK location if not set via environment
export WASI_SDK_PREFIX="${WASI_SDK_PREFIX:-/opt/wasi-sdk}"

if [ ! -f "$WASI_SDK_PREFIX/bin/clang" ]; then
    echo "ERROR: WASI SDK clang not found at: $WASI_SDK_PREFIX/bin/clang"
    echo "Please set WASI_SDK_PREFIX or install WASI SDK to /opt/wasi-sdk"
    echo "Download from: https://github.com/WebAssembly/wasi-sdk/releases"
    exit 1
fi

echo "Using WASI SDK at: $WASI_SDK_PREFIX"
echo "WASI SDK clang version: $($WASI_SDK_PREFIX/bin/clang --version | head -n1)"

# Check for WASI runtime
WASI_RUNTIME="${WASI_RUNTIME:-wasmtime}"
if ! command -v "$WASI_RUNTIME" &> /dev/null; then
    echo "ERROR: WASI runtime ($WASI_RUNTIME) not found."
    echo "Please install wasmtime or another WASI runtime."
    echo "Download from: https://wasmtime.dev/"
    exit 1
fi

echo "Using WASI runtime: $WASI_RUNTIME"
$WASI_RUNTIME --version || true

# GoogleTest filter to exclude tests that require fork() or sockets (not supported in WASI)
# Threading tests are also excluded since WASI P2 doesn't support pthreads.
#
# Excluded tests:
# - *Socket*/*socket*: Require BSD sockets which WASI P2 doesn't support
# - *Fork*/*fork*: WASI doesn't support fork() for multiprocessing
# - *Thread*/*thread*: Threading tests require pthreads
# - BIOTest.CloseFlags: Requires dup() which WASI doesn't support
# - BIOTest.Gets: Requires temporary file creation in system temp directory
# - BIOTest.FileMode: Requires temporary file creation in system temp directory
# - SSLTest.EmptyClientCAList: Requires file I/O operations not available in WASI sandbox
WASI_GTEST_FILTER="-*Socket*:*socket*:*Fork*:*fork*:*Thread*:*thread*:BIOTest.CloseFlags:BIOTest.Gets:BIOTest.FileMode:SSLTest.EmptyClientCAList"

# Function to build AWS-LC for WASI with testing enabled
function run_wasi_build {
    echo "Building AWS-LC for WASI (Release) with testing enabled..."

    rm -rf "${BUILD_ROOT:?}"
    mkdir -p "$BUILD_ROOT"
    cd "$BUILD_ROOT"

    ${CMAKE_COMMAND} \
        -GNinja \
        -DCMAKE_TOOLCHAIN_FILE="${SRC_ROOT}/util/wasi-sdk-toolchain.cmake" \
        -DCMAKE_BUILD_TYPE=Release \
        -DDISABLE_CPU_JITTER_ENTROPY=ON \
        -DDISABLE_GO=ON \
        -DDISABLE_PERL=ON \
        -DBUILD_TESTING=ON \
        -DBUILD_TOOL=OFF \
        "$SRC_ROOT"

    cmake --build . --parallel

    cd "$SRC_ROOT"
}

# Function to run a single WASI test using wasmtime
function run_single_wasi_test {
    local test_path=$1
    shift
    local test_args=("$@")
    local test_name
    test_name=$(basename "$test_path")

    echo ""
    echo "========================================"
    echo "Running ${test_name}..."
    echo "========================================"

    # Run WASI test via wasmtime
    # --dir=. grants access to current directory for any file operations
    if ! $WASI_RUNTIME --dir=. "${test_path}" -- "${test_args[@]}"; then
        echo "ERROR: ${test_name} failed"
        return 1
    fi

    echo "${test_name} passed"
    return 0
}

# Function to run WASI tests
function run_wasi_tests {
    echo "Running WASI tests using ${WASI_RUNTIME}..."
    echo "Threading: disabled (WASI P2 does not support pthreads)"
    echo "Sockets: disabled (WASI P2 does not support BSD sockets)"
    echo "Test filter: ${WASI_GTEST_FILTER}"

    cd "$BUILD_ROOT"

    local failed_tests=()

    # Run urandom_test (simpler test, good for basic verification)
    if ! run_single_wasi_test "crypto/urandom_test"; then
        failed_tests+=("urandom_test")
    fi

    # Run crypto_test (excluding fork, socket, and thread tests)
    if ! run_single_wasi_test "crypto/crypto_test" --gtest_filter="${WASI_GTEST_FILTER}"; then
        failed_tests+=("crypto_test")
    fi

    # Run ssl_test (excluding fork, socket, and thread tests)
    if ! run_single_wasi_test "ssl/ssl_test" --gtest_filter="${WASI_GTEST_FILTER}"; then
        failed_tests+=("ssl_test")
    fi

    cd "$SRC_ROOT"

    if [ ${#failed_tests[@]} -ne 0 ]; then
        echo ""
        echo "========================================"
        echo "FAILED TESTS: ${failed_tests[*]}"
        echo "========================================"
        exit 1
    fi

    echo ""
    echo "All WASI tests passed successfully!"
}

# Main execution

echo "========================================"
echo "AWS-LC WASI SDK Build & Test"
echo "========================================"
echo ""
echo "Target: wasm32-wasip2"
echo "Threading support: disabled (WASI P2 does not support pthreads)"
echo "Socket support: disabled (WASI P2 does not support BSD sockets)"
echo ""

run_wasi_build
run_wasi_tests

echo ""
echo "All WASI build and test runs completed successfully!"
