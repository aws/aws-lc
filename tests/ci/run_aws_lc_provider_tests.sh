#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Build the AWS-LC OpenSSL provider in its shipping configuration and assert
# that the module and its required entry point were produced. The entry point is
# intentionally not loaded because its implementation is a stub.

set -euo pipefail

function banner {
  echo ""
  echo "=========================================================================="
  echo "$*"
  echo "=========================================================================="
}

function fail {
  echo >&2 ""
  echo >&2 "FAILED: $*"
  exit 1
}

[[ "$(uname -s)" == "Linux" ]] \
  || fail "this script builds the shipping configuration and is Linux only; got $(uname -s)"

source tests/ci/common_posix_setup.sh

openssl_provider_tag='openssl-3.5.5'
openssl_url='https://github.com/openssl/openssl.git'
scratch_folder="${SYS_ROOT}/awslc-provider-scratch"
install_dir="${scratch_folder}/openssl_install_dir"

MODULE_NAME="awslc.so"

banner "Building OpenSSL ${openssl_provider_tag}"

mkdir -p "${scratch_folder}"
rm -rf "${scratch_folder:?}"/*

build_openssl_no_debug "${openssl_provider_tag}"

OPENSSL_ROOT="${install_dir}/openssl-${openssl_provider_tag}"

[[ -f "${OPENSSL_ROOT}/include/openssl/core_dispatch.h" ]] \
  || fail "built ${openssl_provider_tag} but ${OPENSSL_ROOT} has no provider headers"

echo ""
echo "OpenSSL prefix: ${OPENSSL_ROOT}"

banner "Building AWS-LC and the provider"

cmake_args=(
  -DCMAKE_BUILD_TYPE=Release
  -DBUILD_SHARED_LIBS=1
  -DENABLE_DIST_PKG=ON
  -DBUILD_AWSLC_PROVIDER=ON
  "-DAWSLC_PROVIDER_OPENSSL_ROOT=${OPENSSL_ROOT}"
)

echo "cmake flags: ${cmake_args[*]}"
run_build "${cmake_args[@]}"
run_cmake_custom_target awslc_provider

banner "Artifacts"

PROVIDER_DIR="${BUILD_ROOT}/provider"
MODULE="${PROVIDER_DIR}/${MODULE_NAME}"

[[ -f "${MODULE}" ]] || fail "no provider module at ${MODULE}"
echo "module: ${MODULE}"

command -v nm > /dev/null 2>&1 || fail "nm is required for the export check"

exported="$(nm -g --defined-only "${MODULE}" 2>/dev/null || true)"
grep -qw 'OSSL_provider_init' <<< "${exported}" \
  || fail "${MODULE} does not export OSSL_provider_init; it will not load"
echo "exports OSSL_provider_init"

banner "Provider build passed"

echo "Covered: the provider module builds and exports OSSL_provider_init."
echo ""
