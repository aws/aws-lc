#!/usr/bin/env bash

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -e

# Symbol version registry checker for AWS-LC CI.
#
# The symbol registry files (crypto/libcrypto.txt, ssl/libssl.txt) are the
# source of truth. Each line is "<symbol> <version_node> <visibility>".
# Visibility is PUBLIC, PRIVATE, or PRIVATE_CXX.
#
# This script checks that the registry is kept up to date with the headers.
#
# Usage: check_symbols.sh <crypto|ssl> <incremental|baseline>
#
# Modes:
#   incremental - Compare registry files between /previous and /next commits.
#                 No build required. Detects symbols added or removed from the
#                 registry between commits. PUBLIC symbol removal is an error;
#                 PRIVATE/PRIVATE_CXX removal is allowed (warning only).
#
#   baseline    - Extract symbols from public and internal headers and verify
#                 every symbol is present in the registry. Detects unregistered
#                 new API. Requires Go and a C compiler in the container.
#
# Exit codes:
#   0 - No problems (additions are warned but allowed)
#   1 - PUBLIC symbol removals detected (ABI break) or unregistered new API
#   2 - Usage error or missing file

CHECK_LIB="$1"
MODE="$2"

if [[ "${CHECK_LIB}" != "crypto" && "${CHECK_LIB}" != "ssl" ]]; then
  echo "Error: first argument must be 'crypto' or 'ssl'"
  exit 2
fi

if [[ "${MODE}" != "incremental" && "${MODE}" != "baseline" ]]; then
  echo "Error: second argument must be 'incremental' or 'baseline'"
  exit 2
fi

REGISTRY_PATH="${CHECK_LIB}/lib${CHECK_LIB}.txt"

if [[ "${CHECK_LIB}" == "crypto" ]]; then
  READ_FLAGS=(-exclude ssl.h -internal-dirs crypto)
else
  READ_FLAGS=(-include ssl.h -internal-dirs ssl -suppress-internal-dirs crypto)
fi

# ---------------------------------------------------------------------------
if [[ "${MODE}" == "incremental" ]]; then
  echo "=========================================="
  echo "Incremental Registry Check: ${CHECK_LIB}"
  echo "=========================================="
  echo "Comparing registry between /previous and /next commits"
  echo ""

  PREV="/previous/${REGISTRY_PATH}"
  NEXT="/next/${REGISTRY_PATH}"

  if [[ ! -f "${PREV}" || ! -f "${NEXT}" ]]; then
    echo "Error: registry file not found in /previous or /next"
    exit 2
  fi

  # Extract and sort symbol names (column 1) from each registry
  awk '{print $1}' "${PREV}" | sort > /tmp/prev_syms.txt
  awk '{print $1}' "${NEXT}" | sort > /tmp/next_syms.txt

  added=$(comm -13 /tmp/prev_syms.txt /tmp/next_syms.txt)
  removed=$(comm -23 /tmp/prev_syms.txt /tmp/next_syms.txt)

  added_count=$(echo "${added}" | grep -c . || true)
  removed_count=$(echo "${removed}" | grep -c . || true)

  echo "Previous: $(wc -l < /tmp/prev_syms.txt) symbols"
  echo "Current:  $(wc -l < /tmp/next_syms.txt) symbols"
  echo ""

  if [[ ${added_count} -gt 0 ]]; then
    echo "⚠️  NEW SYMBOLS IN REGISTRY (${added_count}):"
    echo "${added}" | head -20
    [[ ${added_count} -gt 20 ]] && echo "... and $((added_count - 20)) more"
    echo ""
    echo "ℹ️  New API registered. Verify util/update_symbol_version.sh was used."
    echo ""
  fi

  if [[ ${removed_count} -gt 0 ]]; then
    # Build a lookup of symbol → visibility from the previous registry
    # Format: "SYMBOL VISIBILITY" (columns 1 and 3)
    awk '{print $1, $3}' "${PREV}" | sort > /tmp/prev_vis.txt

    # Separate removed symbols into PUBLIC and PRIVATE/PRIVATE_CXX
    public_removed=""
    private_removed=""
    public_removed_count=0
    private_removed_count=0

    while IFS= read -r sym; do
      vis=$(awk -v s="${sym}" '$1 == s { print $2 }' /tmp/prev_vis.txt)
      if [[ "${vis}" == "PRIVATE" || "${vis}" == "PRIVATE_CXX" || "${vis}" == "PRIVATE_CXX_CLASS" ]]; then
        private_removed="${private_removed}${sym}\n"
        private_removed_count=$((private_removed_count + 1))
      else
        public_removed="${public_removed}${sym}\n"
        public_removed_count=$((public_removed_count + 1))
      fi
    done <<< "${removed}"

    if [[ ${private_removed_count} -gt 0 ]]; then
      echo "⚠️  PRIVATE SYMBOLS REMOVED FROM REGISTRY (${private_removed_count}):"
      echo -e "${private_removed}" | head -20
      [[ ${private_removed_count} -gt 20 ]] && echo "... and $((private_removed_count - 20)) more"
      echo ""
      echo "ℹ️  Private API symbols removed. This is allowed but noted."
      echo ""
    fi

    if [[ ${public_removed_count} -gt 0 ]]; then
      echo "❌ PUBLIC SYMBOLS REMOVED FROM REGISTRY (${public_removed_count}):"
      echo -e "${public_removed}" | head -20
      [[ ${public_removed_count} -gt 20 ]] && echo "... and $((public_removed_count - 20)) more"
      echo ""
      echo "🛑 ABI BREAK: removing public symbols from the registry breaks compatibility."
      echo "   If intentional, increment ABI_VERSION in CMakeLists.txt and"
      echo "   start a new version series."
      exit 1
    fi
  fi

  echo "✅ Incremental registry check passed"
  exit 0

# ---------------------------------------------------------------------------
elif [[ "${MODE}" == "baseline" ]]; then
  echo "=========================================="
  echo "Baseline Registry Check: ${CHECK_LIB}"
  echo "=========================================="
  echo "Checking that all header symbols are registered"
  echo ""

  cd /workspace

  if [[ ! -f "${REGISTRY_PATH}" ]]; then
    echo "Error: registry not found: ${REGISTRY_PATH}"
    echo "Run util/generate_initial_version_scripts.sh first."
    exit 2
  fi

  # Extract current symbols from headers (public + internal, with visibility)
  go run ./util/read_public_symbols \
    -include-dir include \
    -source-root . \
    -emit-visibility \
    "${READ_FLAGS[@]}" \
    -out /tmp/header_syms.txt 2>/dev/null

  # Extract registered symbol names (column 1)
  awk '{print $1}' "${REGISTRY_PATH}" | sort > /tmp/registry_syms.txt
  awk '{print $1}' /tmp/header_syms.txt | sort > /tmp/header_sym_names.txt

  # Symbols in headers but NOT in registry = unregistered new API
  unregistered=$(comm -23 /tmp/header_sym_names.txt /tmp/registry_syms.txt)
  unregistered_count=$(echo "${unregistered}" | grep -c . || true)

  # Symbols in registry but NOT in headers = potentially removed or platform-specific
  missing=$(comm -23 /tmp/registry_syms.txt /tmp/header_sym_names.txt)
  missing_count=$(echo "${missing}" | grep -c . || true)

  echo "Header symbols:     $(wc -l < /tmp/header_sym_names.txt)"
  echo "Registered symbols: $(wc -l < /tmp/registry_syms.txt)"
  echo ""

  if [[ ${missing_count} -gt 0 ]]; then
    echo "⚠️  REGISTERED SYMBOLS NOT IN HEADERS (${missing_count}):"
    echo "${missing}" | head -20
    [[ ${missing_count} -gt 20 ]] && echo "... and $((missing_count - 20)) more"
    echo ""
    echo "ℹ️  These may be platform-specific (e.g. FIPS-only, ARM-specific),"
    echo "   removed APIs, or unimplemented declarations."
    echo ""
  fi

  if [[ ${unregistered_count} -gt 0 ]]; then
    echo "❌ UNREGISTERED SYMBOLS (${unregistered_count}):"
    echo "${unregistered}" | head -20
    [[ ${unregistered_count} -gt 20 ]] && echo "... and $((unregistered_count - 20)) more"
    echo ""
    echo "🛑 New symbols are not in the registry."
    echo "   Run: util/update_symbol_version.sh <version>"
    exit 1
  fi

  echo "✅ Baseline registry check passed"
  exit 0
fi
