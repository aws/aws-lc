#!/usr/bin/env bash
# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Assigns newly added public and internal API symbols to a version node and
# regenerates the version scripts.
#
# When new OPENSSL_EXPORT symbols are added to public or internal headers,
# this script:
#   1. Extracts the current full symbol set from headers (public + internal)
#   2. Identifies symbols not yet in the registry (new API)
#   3. Appends them to the registry with the chosen version node and visibility
#   4. Re-sorts the registry and regenerates the map files
#
# Usage: ./util/update_symbol_version.sh --current
#        ./util/update_symbol_version.sh <version>
#
#   --current   Add the new symbols to the current (newest) node already in the
#               registry. This is the common case: while a node is still open,
#               new API accumulates in it.
#   <version>   Open a NEW node (e.g. AWS_LC_1.1) and add the new symbols to it.
#               Opening a node closes the current one, so this is a release-level
#               decision: use it when the current node has been closed to further
#               additions, or when starting a new ABI series.
#
# Exactly one of the two must be given: the node is always an explicit choice,
# never a default.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

usage() {
  echo "Usage: $0 --current      # add new symbols to the current (newest) node"
  echo "       $0 <version>     # open a new node, e.g. AWS_LC_1.1"
  echo ""
  echo "Exactly one argument is required; the version node is always explicit."
}

if [[ $# -ne 1 ]]; then
  usage
  exit 1
fi

MODE_ARG="$1"

if [[ "${MODE_ARG}" == "-h" || "${MODE_ARG}" == "--help" ]]; then
  usage
  exit 0
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

# Print the newest version node in a registry. Nodes are AWS_LC_<major>.<minor>,
# so sort numerically on each component rather than lexically: that keeps
# AWS_LC_1.10 after AWS_LC_1.9 instead of before it.
newest_node() {
  awk 'NF { print $2 }' "$1" | sort -u | sed 's/^AWS_LC_//' | \
    sort -t. -k1,1n -k2,2n | tail -1 | sed 's/^/AWS_LC_/'
}

if [[ "${MODE_ARG}" == "--current" ]]; then
  # libcrypto and libssl share one symbol version namespace, so their newest
  # nodes must agree; if they have diverged, "current" is ambiguous and the
  # caller has to say which node they mean.
  CRYPTO_CURRENT=$(newest_node "${CRYPTO_REGISTRY}")
  SSL_CURRENT=$(newest_node "${SSL_REGISTRY}")

  if [[ -z "${CRYPTO_CURRENT}" || -z "${SSL_CURRENT}" ]]; then
    echo "Error: could not determine the current version node from the registry."
    echo "Run util/generate_initial_version_scripts.sh first."
    exit 1
  fi

  if [[ "${CRYPTO_CURRENT}" != "${SSL_CURRENT}" ]]; then
    echo "Error: registries disagree on the current version node:"
    echo "  ${CRYPTO_REGISTRY}: ${CRYPTO_CURRENT}"
    echo "  ${SSL_REGISTRY}: ${SSL_CURRENT}"
    echo "libcrypto and libssl share one version namespace. Pass the node"
    echo "explicitly instead of --current."
    exit 1
  fi

  NEW_VERSION="${CRYPTO_CURRENT}"
  echo "Adding to current version node: ${NEW_VERSION}"
else
  NEW_VERSION="${MODE_ARG}"

  # Validate version format
  if ! [[ "${NEW_VERSION}" =~ ^AWS_LC_[0-9]+\.[0-9]+$ ]]; then
    echo "Error: version must match AWS_LC_X.Y (e.g. AWS_LC_1.1), got: ${NEW_VERSION}"
    echo ""
    usage
    exit 1
  fi

  # A new node must actually be new. Reusing an existing node is a valid
  # operation, but it has to be requested as such via --current so the choice
  # is deliberate rather than a typo in a version number.
  # Use -F so the '.' in the version (e.g. AWS_LC_1.0) is matched literally
  # rather than as a regex wildcard.
  if awk '{print $2}' "${CRYPTO_REGISTRY}" | grep -Fqx "${NEW_VERSION}" 2>/dev/null || \
     awk '{print $2}' "${SSL_REGISTRY}" | grep -Fqx "${NEW_VERSION}" 2>/dev/null; then
    echo "Error: ${NEW_VERSION} already exists in the registry."
    echo ""
    echo "To add the new symbols to the current node, run:"
    echo "  $0 --current"
    echo "To open a different new node, pass a version that does not exist yet."
    exit 1
  fi

  echo "Opening new version node: ${NEW_VERSION}"
fi

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
  -out "${TMPDIR}/all_crypto.txt"

go run "${SOURCE_ROOT}/util/read_public_symbols" \
  -include-dir "${SOURCE_ROOT}/include" \
  -source-root "${SOURCE_ROOT}" \
  -include ssl.h \
  -internal-dirs ssl \
  -suppress-internal-dirs crypto \
  -emit-visibility \
  -out "${TMPDIR}/all_ssl.txt"

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

# wc -l pads its output, which would render as "(       5)" in the summary
# below; strip the padding so the counts read cleanly.
NEW_CRYPTO=$(wc -l < "${TMPDIR}/new_crypto_names.txt" | tr -d '[:space:]')
NEW_SSL=$(wc -l < "${TMPDIR}/new_ssl_names.txt" | tr -d '[:space:]')

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
#
# The re-sort runs under LC_ALL=C so the registry stays in byte order. That is
# the order generate_version_script emits symbols in, and the order the
# committed registries are already in; sorting under a UTF-8 locale instead
# would silently rewrite the whole file and bury the real change in a
# thousands-line reordering diff.
if [[ ${NEW_CRYPTO} -gt 0 ]]; then
  while IFS= read -r sym; do
    vis=$(awk -v s="${sym}" '$1 == s { print $2 }' "${TMPDIR}/all_crypto.txt")
    echo "${sym} ${NEW_VERSION} ${vis}"
  done < "${TMPDIR}/new_crypto_names.txt" >> "${CRYPTO_REGISTRY}"
  LC_ALL=C sort -o "${CRYPTO_REGISTRY}" "${CRYPTO_REGISTRY}"
fi

if [[ ${NEW_SSL} -gt 0 ]]; then
  while IFS= read -r sym; do
    vis=$(awk -v s="${sym}" '$1 == s { print $2 }' "${TMPDIR}/all_ssl.txt")
    echo "${sym} ${NEW_VERSION} ${vis}"
  done < "${TMPDIR}/new_ssl_names.txt" >> "${SSL_REGISTRY}"
  LC_ALL=C sort -o "${SSL_REGISTRY}" "${SSL_REGISTRY}"
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
echo "Symbols added to ${NEW_VERSION}. Commit these files together:"
echo "  ${CRYPTO_REGISTRY}"
echo "  ${SSL_REGISTRY}"
echo "  ${CRYPTO_MAP}"
echo "  ${SSL_MAP}"
