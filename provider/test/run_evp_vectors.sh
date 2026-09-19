#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Drive OpenSSL's own EVP known-answer vectors through the provider, using the
# pinned OpenSSL source tree's evp_test binary over its stock data files. This
# test suite has a number of caveats though. Mainly, we can't strongly assert
# that AWS-LC answered each vector. Our signal is that given a mixture of
# aws-lc-provider (preferred) and the OpenSSL default (fallback) providers
# loaded, all of the test vectors pass.
#
# What is asserted per data file is the case count, the skip count, and a fetch
# count per algorithm name, not merely that the run exited 0: a case whose init
# fails abandons the remainder, so "0 errors" also describes a run that stopped
# after the first case.
#
# Exits 0 when every expectation is met and non-zero otherwise.

set -euo pipefail

fail() {
  echo "FAILED: $*" >&2
  exit 1
}

OPENSSL_SRC="$1"
EXPECTED_TAG="$2"
MODULE_DIR="$3"

export LC_ALL=C

PROVIDER_CNF="$(dirname "${BASH_SOURCE[0]}")/provider.cnf"

EVP_TEST="${OPENSSL_SRC}/test/evp_test"
WRAP="${OPENSSL_SRC}/util/wrap.pl"
DATA_DIR="${OPENSSL_SRC}/test/recipes/30-test_evp_data"

PROVIDER_NAME="awslc"

# One line per data file: name, expected case count, expected skip count, then a
# required fetch count per algorithm the provider backs.
#
#   cases   Known answers in the file.
#   skips   Cases evp_test declines to run.
#   fetches Times evp_test reported fetching that specific algorithm name.
#
# Algorithms the provider does not back are the default provider's to serve and
# are left unconstrained.
EXPECTATIONS=(
  "evpmd_sha.txt 74 0 SHA224:3 SHA256:3 SHA384:3 SHA512:3 SHA512-224:7 SHA512-256:7 shA512:1"
)

# --------------------------------------------------------------------------
# Shared parsing
# --------------------------------------------------------------------------

# "Completed %d tests with %d errors and %d skipped", from the test framework's
# own summary line, as "<tests> <errors> <skips>".
completion_counts() {
  sed -n \
    's/.*Completed \([0-9][0-9]*\) tests with \([0-9][0-9]*\) errors and \([0-9][0-9]*\) skipped.*/\1 \2 \3/p' |
    tail -n 1
}

# From the "<alg> is fetched" lines evp_test prints. Printed only when
# EVP_MD_fetch returned an implementation, so it distinguishes a real fetch from
# the built-in name table evp_test falls back to when a fetch fails.
fetch_histogram() {
  awk '
    / is fetched$/ {
      line = $0
      sub(/[ \t]+is fetched$/, "", line)
      count = split(line, parts, /[ \t]+/)
      print parts[count]
    }
  ' |
    sort |
    uniq -c |
    awk '{ print $2 ":" $1 }'
}

fetch_count() {
  awk -F: -v name="$1" '$1 == name { print $2 }' <<<"$2"
}

export OPENSSL_MODULES="${MODULE_DIR}"

# --------------------------------------------------------------------------
# The vectors
# --------------------------------------------------------------------------

files_run=0
files_passed=0
files_with_skips=0
files_failed=0

for entry in "${EXPECTATIONS[@]}"; do
  read -r datafile want_cases want_skips want_fetches <<<"${entry}"
  files_run=$((files_run + 1))

  # Run in place: wrap.pl bakes absolute configure-time paths. Its completion line
  # and fetch stream go to stderr, hence the merge.
  output="$(
    perl "${WRAP}" "${EVP_TEST}" -config "${PROVIDER_CNF}" \
      "${DATA_DIR}/${datafile}" 2>&1
  )" && run_status=0 || run_status=$?

  counts="$(completion_counts <<<"${output}")"
  if [[ -z "${counts}" ]]; then
    {
      echo "FAIL ${datafile}: no completion line, evp_test exited ${run_status}"
      sed 's/^/    /' <<<"${output}"
    } >&2
    fail "${datafile} did not run to completion"
  fi
  read -r got_cases got_errors got_skips <<<"${counts}"
  got_fetches="$(fetch_histogram <<<"${output}")"

  problems=()
  [[ "${run_status}" -eq 0 ]] || problems+=("evp_test exited ${run_status}")
  [[ "${got_errors}" -eq 0 ]] || problems+=("${got_errors} vector errors")
  [[ "${got_cases}" -eq "${want_cases}" ]] ||
    problems+=("ran ${got_cases} cases, expected ${want_cases}")
  [[ "${got_skips}" -eq "${want_skips}" ]] ||
    problems+=("skipped ${got_skips} cases, expected ${want_skips}")

  for spec in ${want_fetches}; do
    name="${spec%%:*}"
    want="${spec##*:}"
    got="$(fetch_count "${name}" "${got_fetches}")"
    [[ "${got:-0}" -eq "${want}" ]] ||
      problems+=("${name} fetched ${got:-0} times, expected ${want}")
  done

  if [[ "${#problems[@]}" -eq 0 ]]; then
    files_passed=$((files_passed + 1))
    echo "PASS ${datafile}: tests=${got_cases} errors=${got_errors}" \
      "skips=${got_skips}, all fetch counts match"
  else
    files_failed=$((files_failed + 1))
    {
      echo "FAIL ${datafile}: tests=${got_cases} errors=${got_errors}" \
        "skips=${got_skips}"
      for problem in "${problems[@]}"; do
        echo "  ${problem}"
      done
      echo "  evp_test output:"
      sed 's/^/    /' <<<"${output}"
    } >&2
  fi

  # Named separately because a skipped case is coverage lost rather than a wrong
  # answer. Every row expects none, so a skip also fails the file.
  if [[ "${got_skips}" -ne 0 ]]; then
    files_with_skips=$((files_with_skips + 1))
    echo "     ${datafile}: ${got_skips} cases skipped and did not run"
  fi
done

echo ""
echo "files run: ${files_run}, passed: ${files_passed}," \
  "with skips: ${files_with_skips}, failed: ${files_failed}"

# Before the statement of what a green run covers, so a failing run cannot print
# that statement.
[[ "${files_failed}" -eq 0 ]] || fail "${files_failed} of ${files_run} vector files"

echo "run_evp_vectors completed successfully."
