#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Assert that frontend objects reference no name in AWS-LC's symbol registry,
# backend registry matches are public and define the expected name/version
# imports, and the final module contains exactly those imports.

set -euo pipefail

fail() {
  echo "FAILED: $*" >&2
  exit 1
}

[[ "$#" -eq 4 ]] ||
  fail "usage: $0 <module> <AWS-LC registry> <backend objects> <frontend objects>"

MODULE="$1"
REGISTRY="$2"
IFS=';' read -r -a backend_objects <<<"$3"
IFS=';' read -r -a frontend_objects <<<"$4"

[[ "$(uname -s)" == "Linux" ]] || fail "ELF linkage verification is Linux only"
[[ -f "${MODULE}" ]] || fail "provider module not found: ${MODULE}"
[[ -f "${REGISTRY}" ]] || fail "symbol registry not found: ${REGISTRY}"
[[ "${#backend_objects[@]}" -gt 0 ]] || fail "no backend objects supplied"
[[ "${#frontend_objects[@]}" -gt 0 ]] || fail "no frontend objects supplied"

command -v nm >/dev/null 2>&1 || fail "nm is required"
command -v objdump >/dev/null 2>&1 || fail "objdump is required"

for object in "${backend_objects[@]}" "${frontend_objects[@]}"; do
  [[ -f "${object}" ]] || fail "object not found: ${object}"
done

export LC_ALL=C

# Object files reveal which side requested a symbol before the final linker
# assigns a library version to it.
collect_undefined() {
  nm -u "$@" 2>/dev/null |
    awk '
      NF > 0 {
        symbol = $NF
        sub(/@.*/, "", symbol)
        if (symbol !~ /:$/) {
          print symbol
        }
      }
    ' |
    sort -u
}

# Convert symbol names on stdin to their name, version, and visibility rows from
# AWS-LC's authoritative registry.
join_registry() {
  awk '
    NR == FNR {
      registry[$1] = $0
      next
    }
    $1 in registry {
      print registry[$1]
    }
  ' "${REGISTRY}" -
}

# Backend matches are the AWS-LC imports the final module must contain. Any
# frontend match is unsafe because the AWS-LC link could capture it.
backend_expected="$(
  collect_undefined "${backend_objects[@]}" |
    join_registry
)"
frontend_overlap="$(
  collect_undefined "${frontend_objects[@]}" |
    join_registry
)"

[[ -n "${backend_expected}" ]] ||
  fail "no backend import matched the AWS-LC registry"

if [[ -n "${frontend_overlap}" ]]; then
  echo "FAILED: frontend imports names exported by AWS-LC:" >&2
  awk '{ print "  " $0 }' <<<"${frontend_overlap}" >&2
  exit 1
fi
echo "OK: frontend imports no AWS-LC symbol"

backend_nonpublic="$(awk '$3 != "PUBLIC"' <<<"${backend_expected}")"
if [[ -n "${backend_nonpublic}" ]]; then
  echo "FAILED: backend imports non-public AWS-LC symbols:" >&2
  awk '{ print "  " $0 }' <<<"${backend_nonpublic}" >&2
  exit 1
fi

expected_imports="$(
  awk '{ print $1, $2 }' <<<"${backend_expected}" |
    sort -u
)"

# Unlike the object files, the final module records the versions the runtime
# loader must satisfy.
module_undefined="$(
  objdump -T "${MODULE}" 2>/dev/null |
    awk '
      /\*UND\*/ {
        version = $(NF - 1)
        gsub(/[()]/, "", version)
        print $NF, version
      }
    ' |
    sort -u
)"

# Include registry names even when they lost their version, plus any AWS_LC_*
# import missing from the registry.
actual_imports="$(
  awk '
    NR == FNR {
      registry[$1] = 1
      next
    }
    $1 in registry || $2 ~ /^AWS_LC_/ {
      print $1, $2
    }
  ' "${REGISTRY}" - <<<"${module_undefined}" |
    sort -u
)"

# Exact equality catches missing or rewritten backend imports and unexpected
# AWS-LC imports introduced outside the backend object list.
if [[ "${actual_imports}" != "${expected_imports}" ]]; then
  echo "FAILED: final AWS-LC imports differ from backend expectations:" >&2
  diff -u \
    --label "expected from backend objects" \
    --label "actual in provider module" \
    <(printf '%s\n' "${expected_imports}") \
    <(printf '%s\n' "${actual_imports}") >&2 ||
    true
  exit 1
fi

backend_count="$(awk 'END { print NR }' <<<"${expected_imports}")"
echo "OK: ${backend_count} public backend imports match their AWS-LC registry versions"
