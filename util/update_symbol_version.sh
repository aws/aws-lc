#!/usr/bin/env bash
# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Assigns newly added public and internal API symbols to a new version node
# and regenerates the version scripts.
#
# When new OPENSSL_EXPORT symbols are added to public or internal headers,
# this script:
#   1. Extracts the current full symbol set from headers (public + internal)
#   2. Identifies symbols not yet in the registry (new API)
#   3. Appends them to the registry with the given version node and visibility
#   4. Re-sorts the registry and regenerates the map files
#
# Usage: ./util/update_symbol_version.sh <version>
# Example: ./util/update_symbol_version.sh AWS_LC_1_0

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 <version>"
  echo "  version: version node for new symbols (e.g. AWS_LC_1_0)"
  exit 1
fi

NEW_VERSION="$1"

# Validate version format
if ! [[ "${NEW_VERSION}" =~ ^AWS_LC_[0-9]+_[0-9]+$ ]]; then
  echo "Error: version must match AWS_LC_X_Y (e.g. AWS_LC_1_0), got: ${NEW_VERSION}"
  exit 1
fi

CRYPTO_REGISTRY="${SOURCE_ROOT}/crypto/libcrypto.txt"
SSL_REGISTRY="${SOURCE_ROOT}/ssl/libssl.txt"
CRYPTO_MAP="${SOURCE_ROOT}/crypto/libcrypto.map"
SSL_MAP="${SOURCE_ROOT}/ssl/libssl.map"

for f in "${CRYPTO_REGISTRY}" "${SSL_REGISTRY}"; do
  if [[ ! -f "${f}" ]]; then
    echo "Error: registry not found: ${f}"
    echo "Run util/generate_initial_version_scripts.sh first."
    exit 1
  fi
done

# Verify the new version is not already present in the registry (check field 2)
if awk '{print $2}' "${CRYPTO_REGISTRY}" | grep -qx "${NEW_VERSION}" 2>/dev/null || \
   awk '{print $2}' "${SSL_REGISTRY}" | grep -qx "${NEW_VERSION}" 2>/dev/null; then
  echo "Error: ${NEW_VERSION} already exists in the registry."
  exit 1
fi

echo "New version: ${NEW_VERSION}"
echo ""

TMPDIR=$(mktemp -d)
trap 'rm -rf "${TMPDIR}"' EXIT

# Extract current symbol sets from headers (public + internal, with visibility)
echo "Extracting current symbols from headers..."
go run "${SOURCE_ROOT}/util/read_public_symbols" \
  -include-dir "${SOURCE_ROOT}/include" \
  -source-root "${SOURCE_ROOT}" \
  -exclude ssl.h \
  -internal-dirs crypto,third_party/jitterentropy \
  -emit-visibility \
  -out "${TMPDIR}/all_crypto.txt" 2>/dev/null

go run "${SOURCE_ROOT}/util/read_public_symbols" \
  -include-dir "${SOURCE_ROOT}/include" \
  -source-root "${SOURCE_ROOT}" \
  -include ssl.h \
  -internal-dirs ssl \
  -suppress-internal-dirs crypto \
  -emit-visibility \
  -out "${TMPDIR}/all_ssl.txt" 2>/dev/null

# Find symbols not yet in the registry
# Registry format: "SYMBOL VERSION [VISIBILITY]" — extract column 1
awk '{ print $1 }' "${CRYPTO_REGISTRY}" | sort > "${TMPDIR}/registered_crypto.txt"
awk '{ print $1 }' "${SSL_REGISTRY}"    | sort > "${TMPDIR}/registered_ssl.txt"

# Header output format: "SYMBOL VISIBILITY" — extract column 1 for comparison
awk '{ print $1 }' "${TMPDIR}/all_crypto.txt" | sort > "${TMPDIR}/all_crypto_names.txt"
awk '{ print $1 }' "${TMPDIR}/all_ssl.txt"    | sort > "${TMPDIR}/all_ssl_names.txt"

comm -23 \
  "${TMPDIR}/all_crypto_names.txt" \
  "${TMPDIR}/registered_crypto.txt" \
  > "${TMPDIR}/new_crypto_names.txt"

comm -23 \
  "${TMPDIR}/all_ssl_names.txt" \
  "${TMPDIR}/registered_ssl.txt" \
  > "${TMPDIR}/new_ssl_names.txt"

NEW_CRYPTO=$(wc -l < "${TMPDIR}/new_crypto_names.txt")
NEW_SSL=$(wc -l < "${TMPDIR}/new_ssl_names.txt")

if [[ ${NEW_CRYPTO} -eq 0 && ${NEW_SSL} -eq 0 ]]; then
  echo "No unregistered symbols found. Nothing to do."
  exit 0
fi

echo "New libcrypto symbols (${NEW_CRYPTO}):"
sed 's/^/  /' "${TMPDIR}/new_crypto_names.txt"
echo ""
echo "New libssl symbols (${NEW_SSL}):"
sed 's/^/  /' "${TMPDIR}/new_ssl_names.txt"
echo ""

# Append new symbols to registries with version and visibility, then re-sort.
# Look up each new symbol's visibility from the header output.
if [[ ${NEW_CRYPTO} -gt 0 ]]; then
  while IFS= read -r sym; do
    vis=$(awk -v s="${sym}" '$1 == s { print $2 }' "${TMPDIR}/all_crypto.txt")
    echo "${sym} ${NEW_VERSION} ${vis}"
  done < "${TMPDIR}/new_crypto_names.txt" >> "${CRYPTO_REGISTRY}"
  sort -o "${CRYPTO_REGISTRY}" "${CRYPTO_REGISTRY}"
fi

if [[ ${NEW_SSL} -gt 0 ]]; then
  while IFS= read -r sym; do
    vis=$(awk -v s="${sym}" '$1 == s { print $2 }' "${TMPDIR}/all_ssl.txt")
    echo "${sym} ${NEW_VERSION} ${vis}"
  done < "${TMPDIR}/new_ssl_names.txt" >> "${SSL_REGISTRY}"
  sort -o "${SSL_REGISTRY}" "${SSL_REGISTRY}"
fi

# Regenerate version scripts
echo "Regenerating version scripts..."
go run "${SOURCE_ROOT}/util/generate_version_script" \
  -in "${CRYPTO_REGISTRY}" \
  -out "${CRYPTO_MAP}" 2>&1

go run "${SOURCE_ROOT}/util/generate_version_script" \
  -in "${SSL_REGISTRY}" \
  -out "${SSL_MAP}" 2>&1

echo ""
echo "Done. Commit these files:"
echo "  ${CRYPTO_REGISTRY}"
echo "  ${SSL_REGISTRY}"
echo "  ${CRYPTO_MAP}"
echo "  ${SSL_MAP}"
