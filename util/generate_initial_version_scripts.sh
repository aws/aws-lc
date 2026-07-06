#!/usr/bin/env bash
# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Regenerates the symbol registry files and GNU ld version scripts for AWS-LC.
#
# The registry files (crypto/libcrypto.txt and ssl/libssl.txt) are the source
# of truth. Each line records a symbol, its version node, and its visibility:
#
#   AES_encrypt AWS_LC_1.0 PUBLIC
#   CRYPTO_once AWS_LC_1.0 PRIVATE
#   ssl_cert_check_key_usage AWS_LC_1.0 PRIVATE_CXX
#
# Visibility values:
#   PUBLIC      - public API from include/openssl/*.h, can never be removed
#   PRIVATE     - internal API from crypto/**/*.h (C linkage), can be removed
#   PRIVATE_CXX - internal API from ssl/**/*.h (C++ linkage), can be removed
#
# The version scripts (crypto/libcrypto.map, ssl/libssl.map) are derived from
# the registry and must be regenerated whenever the registry changes.
#
# To add new symbols in a future release, use update_symbol_version.sh instead.
#
# Usage: ./util/generate_initial_version_scripts.sh [--cc COMPILER]

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
CC_FLAG="${CC:-cc}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --cc) CC_FLAG="$2"; shift 2 ;;
    *) echo "Unknown argument: $1"; exit 1 ;;
  esac
done

# The baseline version node for a from-scratch bootstrap. This is intentionally
# fixed: this script only ever establishes the initial node. Later additions go
# through update_symbol_version.sh <version>, which takes the node as an argument
# rather than hardcoding it. The major component corresponds to ABI_VERSION in
# CMakeLists.txt (bumped only on an ABI break).
INITIAL_VERSION="AWS_LC_1.0"
CRYPTO_REGISTRY="${SOURCE_ROOT}/crypto/libcrypto.txt"
SSL_REGISTRY="${SOURCE_ROOT}/ssl/libssl.txt"
CRYPTO_MAP="${SOURCE_ROOT}/crypto/libcrypto.map"
SSL_MAP="${SOURCE_ROOT}/ssl/libssl.map"

echo "Step 1: Building shared libraries for validation..."
BUILD_DIR="$(mktemp -d)"
rm -rf "${BUILD_DIR}"
# This build only produces libraries to validate the extracted symbols against
# (via read_public_symbols -validate-against); it does not need symbol
# versioning. Crucially, building with -DENABLE_DIST_PKG=ON would require the
# .map files to already exist (apply_version_script fatal-errors otherwise),
# which is a chicken-and-egg problem for a script whose job is to regenerate
# those .map files from scratch. Instead build with SONAME enabled
# (ENABLE_PRE_SONAME_BUILD=OFF, so the libraries keep the -awslc suffix the
# find globs below expect) but ENABLE_DIST_PKG=OFF (so no version script is
# required or applied).
cmake -B "${BUILD_DIR}" -S "${SOURCE_ROOT}" \
  -DBUILD_SHARED_LIBS=ON \
  -DENABLE_DIST_PKG=OFF \
  -DENABLE_PRE_SONAME_BUILD=OFF \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -GNinja
ninja -C "${BUILD_DIR}" crypto ssl

LIBCRYPTO_SO=$(find "${BUILD_DIR}/crypto" -name 'libcrypto-awslc.so.*.*.*' | head -1)
LIBSSL_SO=$(find "${BUILD_DIR}/ssl" -name 'libssl-awslc.so.*.*.*' | head -1)

if [ -z "${LIBCRYPTO_SO}" ] || [ -z "${LIBSSL_SO}" ]; then
  echo "Error: shared libraries not found after build"
  exit 1
fi

echo ""
echo "Step 2: Extracting symbols from headers (public + internal)..."

# libcrypto: public headers (excluding ssl.h) + crypto internal headers
go run "${SOURCE_ROOT}/util/read_public_symbols" \
  -include-dir "${SOURCE_ROOT}/include" \
  -source-root "${SOURCE_ROOT}" \
  -cc "${CC_FLAG}" \
  -exclude ssl.h \
  -internal-dirs crypto,third_party/jitterentropy \
  -emit-visibility \
  -validate-against "${LIBCRYPTO_SO}" \
  -out /tmp/libcrypto_headersyms.txt 2>&1

# libssl: ssl.h only + ssl internal headers (suppress crypto internals)
go run "${SOURCE_ROOT}/util/read_public_symbols" \
  -include-dir "${SOURCE_ROOT}/include" \
  -source-root "${SOURCE_ROOT}" \
  -cc "${CC_FLAG}" \
  -include ssl.h \
  -internal-dirs ssl \
  -suppress-internal-dirs crypto \
  -emit-visibility \
  -validate-against "${LIBSSL_SO}" \
  -out /tmp/libssl_headersyms.txt 2>&1

echo ""
echo "Step 3: Writing symbol registry files (${INITIAL_VERSION})..."

# Write registry: "<symbol> AWS_LC_1.0 <visibility>" sorted by symbol name.
# The extractor emits two columns ("SYMBOL VISIBILITY"); we insert the version
# node as the middle column to produce the three-column registry format. The
# temp files are named *_headersyms to distinguish them (two columns, no
# version) from the registry files (three columns, versioned).
#
# write_registry sorts the rows into the registry, then re-checks the result
# with `sort -c` on the symbol column: if a duplicate symbol slipped through
# (which would silently collapse an entry), the check aborts the script.
write_registry() {
  local src="$1" dest="$2"
  awk -v ver="${INITIAL_VERSION}" '{ print $1, ver, $2 }' "${src}" | sort > "${dest}"
  if ! sort -c -u -k1,1 "${dest}" 2>/dev/null; then
    echo "Error: duplicate symbol(s) in generated registry ${dest}" >&2
    awk '{ print $1 }' "${dest}" | sort | uniq -d >&2
    exit 1
  fi
}

write_registry /tmp/libcrypto_headersyms.txt "${CRYPTO_REGISTRY}"
write_registry /tmp/libssl_headersyms.txt "${SSL_REGISTRY}"

echo ""
echo "Step 4: Generating version scripts from registry..."

go run "${SOURCE_ROOT}/util/generate_version_script" \
  -in "${CRYPTO_REGISTRY}" \
  -out "${CRYPTO_MAP}" 2>&1

go run "${SOURCE_ROOT}/util/generate_version_script" \
  -in "${SSL_REGISTRY}" \
  -out "${SSL_MAP}" 2>&1

echo ""
echo "Done:"
echo "  ${CRYPTO_REGISTRY}  ($(wc -l < "${CRYPTO_REGISTRY}") symbols)"
echo "  ${SSL_REGISTRY}     ($(wc -l < "${SSL_REGISTRY}") symbols)"
echo "  ${CRYPTO_MAP}"
echo "  ${SSL_MAP}"
