#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# CI script for testing AWS-LC Emscripten builds
#
# This script builds AWS-LC for WebAssembly and runs the crypto_test and ssl_test
# test binaries using Node.js.
#
# Prerequisites:
#   - EMSDK_PATH environment variable must be set to the Emscripten SDK location
#   - Emscripten SDK must be installed and activated
#   - CMake 3.5 or later
#   - Ninja (recommended) or Make
#   - Node.js 16+ (for running WASM test binaries with pthread support)
#
# Environment Variables:
#   EMSDK_PATH      - Path to the Emscripten SDK (required)
#
# Note: Threading is enabled via Emscripten's pthread implementation using
# Web Workers and SharedArrayBuffer. Some tests that require fork() or sockets
# are still skipped as these features are not supported in WASM.

set -ex

source tests/ci/common_posix_setup.sh

# Check if EMSDK_PATH is set
if [ -z "$EMSDK_PATH" ]; then
    echo "EMSDK_PATH environment variable is not set."
    echo "Please set EMSDK_PATH to your Emscripten SDK location."
    echo "Example: export EMSDK_PATH=/path/to/emsdk"
    exit 1
fi

# Check if EMSDK directory exists
if [ ! -d "$EMSDK_PATH" ]; then
    echo "Emscripten SDK not found at: $EMSDK_PATH"
    echo "Please verify EMSDK_PATH is set correctly."
    exit 1
fi

# Source the Emscripten environment
echo "Setting up Emscripten environment from: $EMSDK_PATH"
source "$EMSDK_PATH/emsdk_env.sh"

# Verify emcc is available
if ! command -v emcc &> /dev/null; then
    echo "emcc not found. Please ensure Emscripten SDK is properly installed."
    echo "You may need to run: cd $EMSDK_PATH && ./emsdk install latest && ./emsdk activate latest"
    exit 1
fi

echo "Using Emscripten version: $(emcc --version | head -n1)"

# Verify Node.js is available (required for running WASM tests)
if ! command -v node &> /dev/null; then
    echo "Node.js not found. Node.js is required to run WASM test binaries."
    echo "Please install Node.js or ensure it is in your PATH."
    exit 1
fi

NODE_VERSION=$(node --version)
echo "Using Node.js version: ${NODE_VERSION}"

# Check Node.js version is 16+ for proper pthread/SharedArrayBuffer support
NODE_MAJOR_VERSION=$(echo "$NODE_VERSION" | sed 's/v\([0-9]*\).*/\1/')
if [ "$NODE_MAJOR_VERSION" -lt 16 ]; then
    echo "WARNING: Node.js version ${NODE_VERSION} may not fully support pthreads."
    echo "Node.js 16+ is recommended for SharedArrayBuffer support."
fi

# GoogleTest filter to exclude tests that require fork() or sockets (not supported in WASM)
# Threading tests are now enabled via Emscripten's pthread implementation.
#
# Excluded tests:
# - *Socket*/*socket*: Require POSIX sockets which need a WebSocket proxy server
# - *Fork*/*fork*: Emscripten doesn't support fork() for multiprocessing
# - ForkDetect.*: Fork detection tests require fork() syscall
# - randTest.Fork: Uses fork() to test RNG behavior across processes
# - treeDrbgJitterentropyTest.BasicFork: Uses fork() for entropy testing
# - randIsolatedTest.BasicFork: Uses fork() for isolated RNG testing
WASM_GTEST_FILTER="-*Socket*:*socket*:*Fork*:*fork*:ForkDetect.*"

# Function to build AWS-LC for WASM with testing enabled
function run_wasm_build {
    local build_type=$1
    shift
    local extra_args=("$@")

    echo "Building AWS-LC for WASM (${build_type}) with testing enabled..."

    rm -rf "${BUILD_ROOT:?}"
    mkdir -p "$BUILD_ROOT"
    cd "$BUILD_ROOT"

    ${CMAKE_COMMAND} \
        -GNinja \
        -DCMAKE_TOOLCHAIN_FILE="${SRC_ROOT}/util/emscripten-toolchain.cmake" \
        -DCMAKE_BUILD_TYPE="${build_type}" \
        -DDISABLE_CPU_JITTER_ENTROPY=ON \
        -DDISABLE_GO=ON \
        -DDISABLE_PERL=ON \
        -DBUILD_TESTING=ON \
        -DBUILD_TOOL=OFF \
        "${extra_args[@]}" \
        "$SRC_ROOT"

    cmake --build . --parallel

    cd "$SRC_ROOT"
}

# Function to verify WASM build artifacts
function verify_wasm_artifacts {
    echo "Verifying WASM build artifacts..."

    # Check for libcrypto
    if [ ! -f "${BUILD_ROOT}/crypto/libcrypto.a" ]; then
        echo "ERROR: libcrypto.a not found"
        exit 1
    fi
    echo "Found: ${BUILD_ROOT}/crypto/libcrypto.a"

    # Check for libssl
    if [ ! -f "${BUILD_ROOT}/ssl/libssl.a" ]; then
        echo "ERROR: libssl.a not found"
        exit 1
    fi
    echo "Found: ${BUILD_ROOT}/ssl/libssl.a"

    # Check for test executables (Emscripten generates .js wrapper files and .wasm binaries)
    local test_binaries=(
        "crypto/crypto_test.js"
        "crypto/urandom_test.js"
        "ssl/ssl_test.js"
    )

    for test_binary in "${test_binaries[@]}"; do
        if [ ! -f "${BUILD_ROOT}/${test_binary}" ]; then
            echo "ERROR: ${test_binary} not found"
            exit 1
        fi
        echo "Found: ${BUILD_ROOT}/${test_binary}"
    done

    # With pthreads enabled, Emscripten also generates worker JS files
    if [ -f "${BUILD_ROOT}/crypto/crypto_test.worker.js" ]; then
        echo "Found: ${BUILD_ROOT}/crypto/crypto_test.worker.js (pthread worker)"
    fi

    echo "Listing generated static libraries:"
    find "${BUILD_ROOT}" -name "*.a" -type f | while read -r lib; do
        echo "  $(basename "$lib"): $(du -h "$lib" | cut -f1)"
    done

    echo "WASM build artifacts verified successfully."
}

# Function to run a single WASM test using Node.js
function run_single_wasm_test {
    local test_path=$1
    shift
    local test_args=("$@")
    local test_name
    test_name=$(basename "$test_path")

    echo ""
    echo "========================================"
    echo "Running ${test_name}..."
    echo "========================================"

    # Run WASM test via the Emscripten-generated JS wrapper using Node.js
    # Note: With PROXY_TO_PTHREAD enabled, main() runs on a worker thread,
    # so pthread operations work correctly without blocking the main thread.
    if ! node "${test_path}" "${test_args[@]}"; then
        echo "ERROR: ${test_name} failed"
        return 1
    fi

    echo "${test_name} passed"
    return 0
}

# Function to run WASM tests using Node.js
function run_wasm_tests {
    echo "Running WASM tests using Node.js..."
    echo "Threading: enabled (via Emscripten pthreads)"
    echo "Test filter: ${WASM_GTEST_FILTER}"

    cd "$BUILD_ROOT"

    local failed_tests=()

    # Run crypto_test (excluding fork and socket tests)
    if ! run_single_wasm_test "crypto/crypto_test.js" --gtest_filter="${WASM_GTEST_FILTER}"; then
        failed_tests+=("crypto_test")
    fi

    # Run urandom_test
    if ! run_single_wasm_test "crypto/urandom_test.js"; then
        failed_tests+=("urandom_test")
    fi

    # Run ssl_test (excluding fork and socket tests)
    if ! run_single_wasm_test "ssl/ssl_test.js" --gtest_filter="${WASM_GTEST_FILTER}"; then
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
    echo "All WASM tests passed successfully!"
}

# Run WASM build and tests in Release mode
echo "Testing AWS-LC WASM build and tests in Release mode."
echo "Threading support: enabled"
run_wasm_build Release
verify_wasm_artifacts
run_wasm_tests

echo ""
echo "All WASM build and test runs completed successfully!"