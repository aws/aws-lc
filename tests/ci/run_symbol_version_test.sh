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

# Directories to remove on exit. Only paths we create ourselves are added here;
# a caller-supplied install_dir is never registered for deletion.
CLEANUP_DIRS=()
cleanup() {
  for d in ${CLEANUP_DIRS[@]+"${CLEANUP_DIRS[@]}"}; do
    [[ -n "${d}" ]] && rm -rf "${d}"
  done
}
trap cleanup EXIT

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

# Check if we're on a supported platform. Symbol versioning requires GNU ld or
# a compatible linker, available on Linux and the BSDs (see docs/SymbolVersioning.md).
case "$OSTYPE" in
  linux-gnu*|freebsd*|openbsd*|netbsd*) ;;
  *)
    print_warn "Symbol versioning only supported on Linux and BSD. Skipping tests."
    exit 0
    ;;
esac

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
  CLEANUP_DIRS+=("${INSTALL_DIR}")

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
# Guard against a malformed .map: the node must be a well-formed AWS_LC_X.Y tag.
if [[ ! "${SYMBOL_VERSION}" =~ ^AWS_LC_[0-9]+\.[0-9]+$ ]]; then
  print_fail "Extracted symbol version is not a well-formed AWS_LC_X.Y string: ${SYMBOL_VERSION}"
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
#
# These are sanity floors, not exact counts: they only assert that the bulk of
# the API is present and versioned, catching a catastrophically empty or
# unversioned build. The registries currently hold ~3000 (libcrypto) and ~640
# (libssl) symbols; the thresholds sit comfortably below those so ordinary API
# growth or removal never trips them. For exact registry/symbol accounting see
# the check_symbols.sh CI jobs.
#
# grep -c exits 1 when it finds no matches, which under `set -e` would abort the
# script; `|| true` keeps a legitimate zero count flowing to the comparison
# below (where it is reported as a failure).
print_test "Check for versioned symbols"

CRYPTO_VERSIONED=$(nm -D "${LIBCRYPTO_SO}" | grep -c "@@${SYMBOL_VERSION}" || true)
print_info "libcrypto: ${CRYPTO_VERSIONED} symbols with @@${SYMBOL_VERSION}"

CRYPTO_MIN_SYMBOLS=3000
if [[ ${CRYPTO_VERSIONED} -gt ${CRYPTO_MIN_SYMBOLS} ]]; then
  print_pass "libcrypto has expected number of versioned symbols"
else
  print_fail "libcrypto has fewer versioned symbols than expected (${CRYPTO_VERSIONED} < ${CRYPTO_MIN_SYMBOLS})"
fi

SSL_VERSIONED=$(nm -D "${LIBSSL_SO}" | grep -c "@@${SYMBOL_VERSION}" || true)
print_info "libssl: ${SSL_VERSIONED} symbols with @@${SYMBOL_VERSION}"

SSL_MIN_SYMBOLS=500
if [[ ${SSL_VERSIONED} -gt ${SSL_MIN_SYMBOLS} ]]; then
  print_pass "libssl has expected number of versioned symbols"
else
  print_fail "libssl has fewer versioned symbols than expected (${SSL_VERSIONED} < ${SSL_MIN_SYMBOLS})"
fi

# Test 4: Check for unversioned exports
print_test "Check for unversioned exported symbols"

# The awk filter selects defined text symbols that leaked out unversioned:
#   $2 == "T"            defined symbol in the text section (exported code)
#   $3 !~ /@/            no version tag (a properly versioned symbol has @@VER)
#   $3 !~ /^_/           exclude toolchain/runtime internals (e.g. _init, _fini)
#   $3 !~ /^OPENSSL_memory/  exclude the OPENSSL_memory_* allocator hooks, which
#                            are intentionally left unversioned
# Anything remaining is a public symbol that escaped versioning.
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

# A small set of ubiquitous, long-stable public symbols used as canaries: they
# confirm that concrete, well-known API is versioned (not just that some large
# count of symbols exists, per Test 3). Any handful of always-present public
# functions works; there is no need to grow this list as new API is added --
# broad coverage is already provided by Test 3 and the check_symbols.sh jobs.
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

  if [[ ! -f "${TEST_PROG}" ]]; then
    # Compilation above failed (already recorded as a FAIL). Flag that the
    # dependent run/link/version checks cannot execute rather than skipping
    # them silently.
    print_fail "Test program binary missing; skipping run/link/version checks"
  else
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

# Test 7: Detect silently dropped exported symbols (independent of the registry)
#
# The registry checks (check_symbols.sh) and the version scripts are both
# derived from util/read_public_symbols. If that extractor misses an
# OPENSSL_EXPORT symbol, the symbol is absent from the registry AND hidden by
# "local: *;" in the version script -- a silent ABI drop that the
# registry-based checks cannot see, because they never look at what the
# compiler actually exports.
#
# To catch this we build the same sources WITHOUT symbol versioning (a plain
# shared build does not set ENABLE_DIST_PKG, so no version script is applied)
# and diff the exported symbol sets. Any symbol exported by the unversioned
# build but missing from the versioned library was hidden by the version
# script and is a silent drop.
print_test "Detect silently dropped exported symbols (independent of registry)"

# Print the sorted set of defined, exported symbol names for a library,
# stripping version tags (func@@AWS_LC_1.0 -> func) and excluding linker /
# runtime internals that are intentionally local in the versioned build.
normalized_exports() {
  local lib="$1"
  nm -D --defined-only "${lib}" 2>/dev/null | \
    awk '$2 ~ /^[TWDBR]$/ { print $3 }' | \
    sed 's/@.*//' | \
    grep -v '^_' | \
    grep -v '^OPENSSL_memory' | \
    sort -u
}

check_dropped_symbols() {
  local name="$1" unversioned_lib="$2" versioned_lib="$3"
  normalized_exports "${unversioned_lib}" > /tmp/uv_${name}.txt
  normalized_exports "${versioned_lib}" > /tmp/v_${name}.txt
  # Symbols exported unversioned but NOT in the versioned library.
  local dropped dropped_count
  dropped=$(comm -23 /tmp/uv_${name}.txt /tmp/v_${name}.txt)
  dropped_count=$(echo "${dropped}" | grep -c . || true)
  if [[ ${dropped_count} -eq 0 ]]; then
    print_pass "${name}: no exported symbols hidden by the version script"
  else
    print_fail "${name}: ${dropped_count} exported symbol(s) silently hidden by the version script"
    print_info "These are exported by the compiler but missing from the registry/.map:"
    echo "${dropped}" | head -10 | sed 's/^/  /'
    [[ ${dropped_count} -gt 10 ]] && print_info "... and $((dropped_count - 10)) more"
  fi
}

# This check requires building an unversioned reference from source. The build
# tools are mandatory: skipping the check would mask exactly the silent-drop
# class of bug it exists to catch, so a missing prerequisite is a failure.
if ! command -v cmake >/dev/null 2>&1; then
  print_fail "cmake not found; required for the silent-drop check. Install cmake."
  exit 1
fi
if ! command -v ninja >/dev/null 2>&1; then
  print_fail "ninja not found; required for the silent-drop check. Install ninja-build."
  exit 1
fi

UNVERSIONED_BUILD=$(mktemp -d)
CLEANUP_DIRS+=("${UNVERSIONED_BUILD}")

print_info "Building unversioned reference libraries (no ENABLE_DIST_PKG)"
# A plain shared build still sets SET_LIB_SONAME (so filenames match the
# versioned -awslc libraries) but does NOT enable symbol versioning.
if ! cmake -GNinja -B "${UNVERSIONED_BUILD}" -S "${SOURCE_ROOT}" \
     -DBUILD_SHARED_LIBS=ON \
     -DCMAKE_BUILD_TYPE=RelWithDebInfo > /dev/null 2>&1 || \
   ! cmake --build "${UNVERSIONED_BUILD}" --target crypto ssl > /dev/null 2>&1; then
  print_fail "Unversioned reference build failed; cannot run silent-drop check"
  exit 1
fi

UV_CRYPTO=$(find "${UNVERSIONED_BUILD}" -name 'libcrypto-awslc.so*' -type f | head -1)
UV_SSL=$(find "${UNVERSIONED_BUILD}" -name 'libssl-awslc.so*' -type f | head -1)

if [[ -z "${UV_CRYPTO}" || -z "${UV_SSL}" ]]; then
  print_fail "Could not locate unversioned reference libraries after build"
  exit 1
fi

# Guard: the unversioned reference must actually be unversioned, otherwise the
# diff is meaningless (both sides hidden identically).
if readelf --version-info "${UV_CRYPTO}" | grep -q "${SYMBOL_VERSION}"; then
  print_fail "Unversioned reference unexpectedly carries version definitions; drop check invalid"
  exit 1
fi

check_dropped_symbols "libcrypto" "${UV_CRYPTO}" "${LIBCRYPTO_SO}"
check_dropped_symbols "libssl" "${UV_SSL}" "${LIBSSL_SO}"

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
