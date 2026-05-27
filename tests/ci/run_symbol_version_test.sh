#!/usr/bin/env bash
# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Test script to validate ELF symbol versioning in AWS-LC
#
# This script verifies that:
# 1. Symbol version scripts are applied correctly
# 2. All exported symbols have proper version tags
# 3. No unversioned symbols leak
# 4. Version definitions are present in shared libraries
# 5. Libraries can be linked and used correctly
#
# Usage: ./tests/ci/run_symbol_version_test.sh [install_dir]
#   If install_dir is provided, uses the installed shared libraries there.
#   Otherwise, builds AWS-LC and tests the build output.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
INSTALL_DIR="${1:-}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

pass_count=0
fail_count=0

print_test() {
  echo ""
  echo "=========================================="
  echo "TEST: $1"
  echo "=========================================="
}

print_pass() {
  echo -e "${GREEN}✓ PASS${NC}: $1"
  pass_count=$((pass_count + 1))
}

print_fail() {
  echo -e "${RED}✗ FAIL${NC}: $1"
  fail_count=$((fail_count + 1))
}

print_warn() {
  echo -e "${YELLOW}⚠ WARN${NC}: $1"
}

print_info() {
  echo "INFO: $1"
}

# Detect library directory (lib or lib64)
get_lib_dir() {
  local dir="$1"
  if [[ -d "${dir}/lib64" ]]; then
    echo "lib64"
  else
    echo "lib"
  fi
}

# Check if we're on a supported platform
if [[ "$OSTYPE" != "linux-gnu"* ]] && [[ "$OSTYPE" != "freebsd"* ]]; then
  print_warn "Symbol versioning only supported on Linux and BSD. Skipping tests."
  exit 0
fi

# Check for required tools
if ! command -v readelf >/dev/null 2>&1; then
  print_fail "readelf not found. Install binutils."
  exit 1
fi

if ! command -v nm >/dev/null 2>&1; then
  print_fail "nm not found. Install binutils."
  exit 1
fi

# Build and install into a temporary directory if no install dir was provided.
if [[ -z "${INSTALL_DIR}" ]]; then
  BUILD_DIR="${SOURCE_ROOT}/build_symbol_test"
  INSTALL_DIR=$(mktemp -d)
  trap 'rm -rf "${INSTALL_DIR}"' EXIT

  print_test "Building and installing AWS-LC with symbol versioning"
  rm -rf "${BUILD_DIR}"
  mkdir -p "${BUILD_DIR}"

  cd "${SOURCE_ROOT}"
  cmake -GNinja -B "${BUILD_DIR}" \
    -DBUILD_SHARED_LIBS=ON \
    -DENABLE_DIST_PKG=ON \
    -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    -DCMAKE_INSTALL_PREFIX="${INSTALL_DIR}"

  if cmake --build "${BUILD_DIR}" --target install; then
    print_pass "Build and install successful"
  else
    print_fail "Build failed"
    exit 1
  fi

  rm -rf "${BUILD_DIR}"
fi

print_info "Using installed libraries from ${INSTALL_DIR}"

LIB_DIR=$(get_lib_dir "${INSTALL_DIR}")
LIBCRYPTO_SO="${INSTALL_DIR}/${LIB_DIR}/libcrypto-awslc.so"
LIBSSL_SO="${INSTALL_DIR}/${LIB_DIR}/libssl-awslc.so"
INCLUDE_DIR="${INSTALL_DIR}/include/aws-lc"
LINK_LIB_DIR="${INSTALL_DIR}/${LIB_DIR}"

# Extract the symbol version tag from the linker map
SYMBOL_VERSION=$(grep -m1 -oP '^AWS_LC_\S+(?= \{)' "${SOURCE_ROOT}/crypto/libcrypto.map")
if [[ -z "${SYMBOL_VERSION}" ]]; then
  print_fail "Could not extract symbol version from libcrypto.map"
  exit 1
fi
print_info "Symbol version: ${SYMBOL_VERSION}"

# Test 1: Verify libraries exist
print_test "Verify shared libraries exist"

if [[ -f "${LIBCRYPTO_SO}" ]]; then
  print_pass "libcrypto-awslc.so exists"
else
  print_fail "libcrypto-awslc.so not found at ${LIBCRYPTO_SO}"
fi

if [[ -f "${LIBSSL_SO}" ]]; then
  print_pass "libssl-awslc.so exists"
else
  print_fail "libssl-awslc.so not found at ${LIBSSL_SO}"
fi

# Test 2: Check version definition sections
print_test "Check version definition sections"

if readelf --version-info "${LIBCRYPTO_SO}" | grep "${SYMBOL_VERSION}" > /dev/null; then
  print_pass "libcrypto has ${SYMBOL_VERSION} version definition"
else
  print_fail "libcrypto missing ${SYMBOL_VERSION} version definition"
fi

if readelf --version-info "${LIBSSL_SO}" | grep "${SYMBOL_VERSION}" > /dev/null; then
  print_pass "libssl has ${SYMBOL_VERSION} version definition"
else
  print_fail "libssl missing ${SYMBOL_VERSION} version definition"
fi

# Test 3: Check versioned symbols
print_test "Check for versioned symbols"

CRYPTO_VERSIONED=$(nm -D "${LIBCRYPTO_SO}" | grep -c "@@${SYMBOL_VERSION}" || true)
print_info "libcrypto: ${CRYPTO_VERSIONED} symbols with @@${SYMBOL_VERSION}"

if [[ ${CRYPTO_VERSIONED} -gt 3000 ]]; then
  print_pass "libcrypto has expected number of versioned symbols"
else
  print_fail "libcrypto has fewer versioned symbols than expected (${CRYPTO_VERSIONED} < 3000)"
fi

SSL_VERSIONED=$(nm -D "${LIBSSL_SO}" | grep -c "@@${SYMBOL_VERSION}" || true)
print_info "libssl: ${SSL_VERSIONED} symbols with @@${SYMBOL_VERSION}"

if [[ ${SSL_VERSIONED} -gt 500 ]]; then
  print_pass "libssl has expected number of versioned symbols"
else
  print_fail "libssl has fewer versioned symbols than expected (${SSL_VERSIONED} < 500)"
fi

# Test 4: Check for unversioned exports
print_test "Check for unversioned exported symbols"

CRYPTO_UNVERSIONED=$(nm -D "${LIBCRYPTO_SO}" | \
  awk '$2 == "T" && $3 !~ /@/ && $3 !~ /^_/ && $3 !~ /^OPENSSL_memory/ { print $3 }' | \
  wc -l)

if [[ ${CRYPTO_UNVERSIONED} -eq 0 ]]; then
  print_pass "libcrypto has no unversioned exports"
else
  print_fail "libcrypto has ${CRYPTO_UNVERSIONED} unversioned exports"
  print_info "First 10 unversioned symbols:"
  nm -D "${LIBCRYPTO_SO}" | \
    awk '$2 == "T" && $3 !~ /@/ && $3 !~ /^_/ && $3 !~ /^OPENSSL_memory/ { print "  " $3 }' | \
    head -10
fi

SSL_UNVERSIONED=$(nm -D "${LIBSSL_SO}" | \
  awk '$2 == "T" && $3 !~ /@/ && $3 !~ /^_/ { print $3 }' | \
  wc -l)

if [[ ${SSL_UNVERSIONED} -eq 0 ]]; then
  print_pass "libssl has no unversioned exports"
else
  print_fail "libssl has ${SSL_UNVERSIONED} unversioned exports"
  print_info "First 10 unversioned symbols:"
  nm -D "${LIBSSL_SO}" | \
    awk '$2 == "T" && $3 !~ /@/ && $3 !~ /^_/ { print "  " $3 }' | \
    head -10
fi

# Test 5: Verify specific API symbols are versioned
print_test "Verify specific API symbols are versioned"

check_symbol() {
  local lib="$1"
  local symbol="$2"
  local expected_version="$3"

  if nm -D "${lib}" | grep "${symbol}@@${expected_version}" > /dev/null; then
    print_pass "${symbol} has correct version (${expected_version})"
  else
    print_fail "${symbol} missing or incorrectly versioned"
  fi
}

check_symbol "${LIBCRYPTO_SO}" "EVP_MD_CTX_new" "${SYMBOL_VERSION}"
check_symbol "${LIBCRYPTO_SO}" "AES_encrypt" "${SYMBOL_VERSION}"
check_symbol "${LIBCRYPTO_SO}" "RSA_new" "${SYMBOL_VERSION}"
check_symbol "${LIBSSL_SO}" "SSL_CTX_new" "${SYMBOL_VERSION}"
check_symbol "${LIBSSL_SO}" "SSL_new" "${SYMBOL_VERSION}"

# Test 6: Link test program
if [[ -d "${INCLUDE_DIR}" ]]; then
  print_test "Test linking against versioned libraries"

  TEST_DIR=$(mktemp -d)
  TEST_PROG="${TEST_DIR}/symbol_version_link_test"
  cat > "${TEST_PROG}.c" << 'EOF'
#include <openssl/evp.h>
#include <openssl/ssl.h>
#include <stdio.h>

int main() {
    EVP_MD_CTX *md_ctx = EVP_MD_CTX_new();
    if (!md_ctx) {
        fprintf(stderr, "EVP_MD_CTX_new failed\n");
        return 1;
    }
    EVP_MD_CTX_free(md_ctx);

    SSL_CTX *ssl_ctx = SSL_CTX_new(TLS_method());
    if (!ssl_ctx) {
        fprintf(stderr, "SSL_CTX_new failed\n");
        return 1;
    }
    SSL_CTX_free(ssl_ctx);

    printf("Symbol versioning test: OK\n");
    return 0;
}
EOF

  if gcc "${TEST_PROG}.c" -o "${TEST_PROG}" \
    -I "${INCLUDE_DIR}" \
    -L "${LINK_LIB_DIR}" \
    -lcrypto-awslc -lssl-awslc \
    -Wl,-rpath,"${LINK_LIB_DIR}"; then
    print_pass "Test program compiled successfully"
  else
    print_fail "Test program compilation failed"
  fi

  if [[ -f "${TEST_PROG}" ]]; then
    if LD_LIBRARY_PATH="${LINK_LIB_DIR}" "${TEST_PROG}"; then
      print_pass "Test program executed successfully"
    else
      print_fail "Test program execution failed"
    fi

    print_test "Verify test program dependencies"

    if ldd "${TEST_PROG}" | grep "libcrypto-awslc.so" > /dev/null; then
      print_pass "Test program linked against libcrypto-awslc.so"
    else
      print_fail "Test program not linked against libcrypto-awslc.so"
    fi

    if ldd "${TEST_PROG}" | grep "libssl-awslc.so" > /dev/null; then
      print_pass "Test program linked against libssl-awslc.so"
    else
      print_fail "Test program not linked against libssl-awslc.so"
    fi

    print_test "Verify symbol versions used by test program"

    if nm -D "${TEST_PROG}" | grep "EVP_MD_CTX_new@${SYMBOL_VERSION}" > /dev/null; then
      print_pass "Test program uses EVP_MD_CTX_new@${SYMBOL_VERSION}"
    else
      print_fail "Test program not using correct EVP_MD_CTX_new version"
    fi

    if nm -D "${TEST_PROG}" | grep "SSL_CTX_new@${SYMBOL_VERSION}" > /dev/null; then
      print_pass "Test program uses SSL_CTX_new@${SYMBOL_VERSION}"
    else
      print_fail "Test program not using correct SSL_CTX_new version"
    fi
  fi

  rm -rf "${TEST_DIR}"
else
  print_info "Skipping link test (no headers found at ${INCLUDE_DIR})"
fi

# Summary
echo ""
echo "=========================================="
echo "TEST SUMMARY"
echo "=========================================="
echo -e "${GREEN}Passed${NC}: ${pass_count}"
if [[ ${fail_count} -gt 0 ]]; then
  echo -e "${RED}Failed${NC}: ${fail_count}"
else
  echo "Failed: ${fail_count}"
fi
echo ""

if [[ ${fail_count} -eq 0 ]]; then
  echo -e "${GREEN}✓ All symbol versioning tests passed!${NC}"
  exit 0
else
  echo -e "${RED}✗ Some symbol versioning tests failed${NC}"
  exit 1
fi
