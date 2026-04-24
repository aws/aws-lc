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
# Usage: ./tests/ci/run_symbol_version_test.sh [build_dir]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
BUILD_DIR="${1:-${SOURCE_ROOT}/build_symbol_test}"

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
  ((pass_count++))
}

print_fail() {
  echo -e "${RED}✗ FAIL${NC}: $1"
  ((fail_count++))
}

print_warn() {
  echo -e "${YELLOW}⚠ WARN${NC}: $1"
}

print_info() {
  echo "INFO: $1"
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

print_test "Building AWS-LC with symbol versioning"
rm -rf "${BUILD_DIR}"
mkdir -p "${BUILD_DIR}"

cd "${SOURCE_ROOT}"
cmake -GNinja -B "${BUILD_DIR}" \
  -DBUILD_SHARED_LIBS=ON \
  -DENABLE_DIST_PKG=ON \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo

ninja -C "${BUILD_DIR}" crypto ssl

if [[ $? -eq 0 ]]; then
  print_pass "Build successful"
else
  print_fail "Build failed"
  exit 1
fi

# Library paths
LIBCRYPTO_SO="${BUILD_DIR}/crypto/libcrypto-awslc.so.0.0.0"
LIBSSL_SO="${BUILD_DIR}/ssl/libssl-awslc.so.0.0.0"

# Test 1: Verify libraries exist
print_test "Verify shared libraries exist"

if [[ -f "${LIBCRYPTO_SO}" ]]; then
  print_pass "libcrypto-awslc.so.0.0.0 exists"
else
  print_fail "libcrypto-awslc.so.0.0.0 not found"
fi

if [[ -f "${LIBSSL_SO}" ]]; then
  print_pass "libssl-awslc.so.0.0.0 exists"
else
  print_fail "libssl-awslc.so.0.0.0 not found"
fi

# Test 2: Check version definition sections
print_test "Check version definition sections"

if readelf --version-info "${LIBCRYPTO_SO}" | grep -q "AWS_LC_1_0"; then
  print_pass "libcrypto has AWS_LC_1_0 version definition"
else
  print_fail "libcrypto missing AWS_LC_1_0 version definition"
fi

if readelf --version-info "${LIBSSL_SO}" | grep -q "AWS_LC_1_0"; then
  print_pass "libssl has AWS_LC_1_0 version definition"
else
  print_fail "libssl missing AWS_LC_1_0 version definition"
fi

# Test 3: Check versioned symbols
print_test "Check for versioned symbols"

CRYPTO_VERSIONED=$(nm -D "${LIBCRYPTO_SO}" | grep -c "@@AWS_LC_1_0" || true)
print_info "libcrypto: ${CRYPTO_VERSIONED} symbols with @@AWS_LC_1_0"

if [[ ${CRYPTO_VERSIONED} -gt 3000 ]]; then
  print_pass "libcrypto has expected number of versioned symbols"
else
  print_fail "libcrypto has fewer versioned symbols than expected (${CRYPTO_VERSIONED} < 3000)"
fi

SSL_VERSIONED=$(nm -D "${LIBSSL_SO}" | grep -c "@@AWS_LC_1_0" || true)
print_info "libssl: ${SSL_VERSIONED} symbols with @@AWS_LC_1_0"

if [[ ${SSL_VERSIONED} -gt 500 ]]; then
  print_pass "libssl has expected number of versioned symbols"
else
  print_fail "libssl has fewer versioned symbols than expected (${SSL_VERSIONED} < 500)"
fi

# Test 4: Check for unversioned exports
print_test "Check for unversioned exported symbols"

# Get all defined global symbols (type T = text/code)
# Filter out those with version suffix (@)
# Exclude weak symbols and special symbols
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

  if nm -D "${lib}" | grep -q "${symbol}@@${expected_version}"; then
    print_pass "${symbol} has correct version (${expected_version})"
  else
    print_fail "${symbol} missing or incorrectly versioned"
  fi
}

# Check some common libcrypto symbols
check_symbol "${LIBCRYPTO_SO}" "EVP_MD_CTX_new" "AWS_LC_1_0"
check_symbol "${LIBCRYPTO_SO}" "AES_encrypt" "AWS_LC_1_0"
check_symbol "${LIBCRYPTO_SO}" "RSA_new" "AWS_LC_1_0"

# Check some libssl symbols
check_symbol "${LIBSSL_SO}" "SSL_CTX_new" "AWS_LC_1_0"
check_symbol "${LIBSSL_SO}" "SSL_new" "AWS_LC_1_0"

# Test 6: Link test program
print_test "Test linking against versioned libraries"

TEST_PROG="${BUILD_DIR}/symbol_version_link_test"
cat > "${TEST_PROG}.c" << 'EOF'
#include <openssl/evp.h>
#include <openssl/ssl.h>
#include <stdio.h>

int main() {
    // Test libcrypto symbols
    EVP_MD_CTX *md_ctx = EVP_MD_CTX_new();
    if (!md_ctx) {
        fprintf(stderr, "EVP_MD_CTX_new failed\n");
        return 1
;
    }
    EVP_MD_CTX_free(md_ctx);

    // Test libssl symbols
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

gcc "${TEST_PROG}.c" -o "${TEST_PROG}" \
  -I "${BUILD_DIR}/include" \
  -L "${BUILD_DIR}/crypto" \
  -L "${BUILD_DIR}/ssl" \
  -lcrypto-awslc -lssl-awslc \
  -Wl,-rpath,"${BUILD_DIR}/crypto:${BUILD_DIR}/ssl"

if [[ $? -eq 0 ]]; then
  print_pass "Test program compiled successfully"
else
  print_fail "Test program compilation failed"
fi

# Run the test program
if LD_LIBRARY_PATH="${BUILD_DIR}/crypto:${BUILD_DIR}/ssl" "${TEST_PROG}"; then
  print_pass "Test program executed successfully"
else
  print_fail "Test program execution failed"
fi

# Check dependencies of test program
print_test "Verify test program dependencies"

if ldd "${TEST_PROG}" | grep -q "libcrypto-awslc.so.0"; then
  print_pass "Test program linked against libcrypto-awslc.so.0"
else
  print_fail "Test program not linked against libcrypto-awslc.so.0"
fi

if ldd "${TEST_PROG}" | grep -q "libssl-awslc.so.0"; then
  print_pass "Test program linked against libssl-awslc.so.0"
else
  print_fail "Test program not linked against libssl-awslc.so.0"
fi

# Test 7: Verify symbol versions in linked program
print_test "Verify symbol versions used by test program"

if nm -D "${TEST_PROG}" | grep -q "EVP_MD_CTX_new@@AWS_LC_1_0"; then
  print_pass "Test program uses EVP_MD_CTX_new@@AWS_LC_1_0"
else
  print_fail "Test program not using correct EVP_MD_CTX_new version"
fi

if nm -D "${TEST_PROG}" | grep -q "SSL_CTX_new@@AWS_LC_1_0"; then
  print_pass "Test program uses SSL_CTX_new@@AWS_LC_1_0"
else
  print_fail "Test program not using correct SSL_CTX_new version"
fi

# Test 8: Check baseline files exist and are non-empty
print_test "Verify baseline files"

CRYPTO_BASELINE="${SOURCE_ROOT}/tests/ci/baselines/symbols/libcrypto-1.0.txt"
SSL_BASELINE="${SOURCE_ROOT}/tests/ci/baselines/symbols/libssl-1.0.txt"

if [[ -f "${CRYPTO_BASELINE}" ]] && [[ -s "${CRYPTO_BASELINE}" ]]; then
  CRYPTO_BASELINE_COUNT=$(wc -l < "${CRYPTO_BASELINE}")
  print_pass "libcrypto baseline exists with ${CRYPTO_BASELINE_COUNT} symbols"
else
  print_fail "libcrypto baseline missing or empty"
fi

if [[ -f "${SSL_BASELINE}" ]] && [[ -s "${SSL_BASELINE}" ]]; then
  SSL_BASELINE_COUNT=$(wc -l < "${SSL_BASELINE}")
  print_pass "libssl baseline exists with ${SSL_BASELINE_COUNT} symbols"
else
  print_fail "libssl baseline missing or empty"
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
