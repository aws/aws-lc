#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

# Build the AWS-LC OpenSSL provider in its shipping configuration and run its
# provider-level unit suite. Linux only, deliberately: ENABLE_DIST_PKG is a
# FATAL_ERROR elsewhere, and without it the two-libcrypto linkage checks below
# have nothing to assert against, so a green run on another platform would claim
# more than it proved. Other platforms are for development; see
# provider/README.md.
#
# The provider is off by default and needs OpenSSL's provider headers, which
# AWS-LC's own tree does not carry, so this script builds the pinned OpenSSL from
# source the way the other CI scripts here build theirs. No runner image ships an
# OpenSSL new enough to use instead, and probing for one would make what the
# provider was compiled against a property of the host.
#
# It takes no arguments and reads no configuration. To build against some other
# OpenSSL, invoke cmake directly with AWSLC_PROVIDER_OPENSSL_ROOT; see
# provider/README.md.

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

# Before sourcing anything, so the refusal is the first thing printed rather than
# being buried under the setup script's environment dump.
[[ "$(uname -s)" == "Linux" ]] \
  || fail "this script builds the shipping configuration and is Linux only; got $(uname -s)"

source tests/ci/common_posix_setup.sh

# The OpenSSL the provider is built and tested against. A tag rather than a
# branch, so the same commit is used until this line changes. 3.5 is the floor:
# earlier 3.x lacks provider interface the front side depends on.
openssl_provider_tag='openssl-3.5.5'

# build_openssl_no_debug reads these three as globals, so the names are its.
openssl_url='https://github.com/openssl/openssl.git'
scratch_folder="${SYS_ROOT}/awslc-provider-scratch"
install_dir="${scratch_folder}/openssl_install_dir"

MODULE_NAME="awslc.so"

# --------------------------------------------------------------------------
# 1. The OpenSSL the provider compiles against
# --------------------------------------------------------------------------

banner "Building OpenSSL ${openssl_provider_tag}"

mkdir -p "${scratch_folder}"
rm -rf "${scratch_folder:?}"/*

# Installs into ${install_dir}/openssl-${1} and deletes its source tree after.
build_openssl_no_debug "${openssl_provider_tag}"

OPENSSL_ROOT="${install_dir}/openssl-${openssl_provider_tag}"

# The provider headers are the actual dependency, and an install can carry a
# libcrypto without them. Checked here so a bad prefix fails with its own message
# rather than as a confusing cmake error.
[[ -f "${OPENSSL_ROOT}/include/openssl/core_dispatch.h" ]] \
  || fail "built ${openssl_provider_tag} but ${OPENSSL_ROOT} has no provider headers"

echo ""
echo "OpenSSL prefix: ${OPENSSL_ROOT}"

# --------------------------------------------------------------------------
# 2. Build AWS-LC with the provider
# --------------------------------------------------------------------------

banner "Building AWS-LC and the provider"

# ENABLE_DIST_PKG is the shipping configuration: ELF symbol versioning binds
# every AWS-LC export to an AWS_LC_1.0 node and suffixes the soname, which is
# what keeps the provider's AWS-LC references from being satisfied by OpenSSL's
# libcrypto.
cmake_args=(
  -DCMAKE_BUILD_TYPE=Release
  -DBUILD_SHARED_LIBS=1
  -DENABLE_DIST_PKG=ON
  -DBUILD_AWSLC_PROVIDER=ON
  "-DAWSLC_PROVIDER_OPENSSL_ROOT=${OPENSSL_ROOT}"
)

echo "cmake flags: ${cmake_args[*]}"
run_build "${cmake_args[@]}"

# Named explicitly rather than relying on the default target having covered
# them, so a renamed or unbuilt target fails here instead of showing up as a
# missing file later.
run_cmake_custom_target awslc_provider awslc_provider_test

# --------------------------------------------------------------------------
# 3. The artifacts must actually exist
# --------------------------------------------------------------------------

banner "Artifacts"

PROVIDER_DIR="${BUILD_ROOT}/provider"
MODULE="${PROVIDER_DIR}/${MODULE_NAME}"

# OpenSSL resolves a provider by bare name and appends the platform's DSO
# suffix, so the file has to be called exactly this to be loadable.
[[ -f "${MODULE}" ]] || fail "no provider module at ${MODULE}"
echo "module: ${MODULE}"

TEST_BINARIES=(
  "${PROVIDER_DIR}/awslc_provider_test"
)

for binary in "${TEST_BINARIES[@]}"; do
  [[ -x "${binary}" ]] || fail "test binary missing or not executable: ${binary}"
  echo "test:   ${binary}"
done

# A provider exports exactly one symbol. Anything else is surface a consumer
# could bind to by accident and that we would then owe compatibility on.
command -v nm > /dev/null 2>&1 || fail "nm is required for the export check"

exported="$(nm -g --defined-only "${MODULE}" 2>/dev/null || true)"
grep -qw 'OSSL_provider_init' <<< "${exported}" \
  || fail "${MODULE} does not export OSSL_provider_init; it will not load"
echo "exports OSSL_provider_init"

# --------------------------------------------------------------------------
# 4. aws-lc-provider binary level asserts
# --------------------------------------------------------------------------
#
# This is the one failure the unit suite cannot see, and the reason this script
# runs where ENABLE_DIST_PKG can be built. Both libcryptos export ~2100
# identically-named symbols, so backend calls can silently bind to OpenSSL's
# implementation rather than AWS-LC's. Only the linkage shows it.
#
# A missing tool is a failure rather than a skip. Skipping would leave the run
# green while the only check that can catch a misbinding never executed.

banner "Linkage"

command -v ldd > /dev/null 2>&1 || fail "ldd is required for the linkage check"

ldd_out="$(ldd "${MODULE}" 2>/dev/null | grep -i crypto || true)"
echo "${ldd_out}"

grep -q 'libcrypto-awslc' <<< "${ldd_out}" \
  || fail "${MODULE} does not depend on libcrypto-awslc; ENABLE_DIST_PKG did not take effect"
if grep -qE 'libcrypto\.so\.(3|1\.1)' <<< "${ldd_out}"; then
  fail "${MODULE} links OpenSSL's libcrypto directly, which reintroduces the collision the provider is split to avoid"
fi
echo "OK: depends on AWS-LC's suffixed libcrypto and not on OpenSSL's"

# Rejects frontend overlap with AWS-LC, then requires the final module's AWS-LC
# imports to match the backend object inventory and crypto/libcrypto.txt.
run_cmake_custom_target awslc_provider_linkage_test

# --------------------------------------------------------------------------
# 5. The suites
# --------------------------------------------------------------------------
#
# awslc_provider_test links OpenSSL's libcrypto and reaches AWS-LC only through
# the provider the loader brings in, which is the arrangement a real consumer
# has.

for binary in "${TEST_BINARIES[@]}"; do
  banner "$(basename "${binary}")"
  "${binary}" || fail "$(basename "${binary}") reported failures"
done

banner "Provider build and unit test passed"

# Say plainly what a green run here covers, so it is not mistaken for more.
echo "Covered: the provider builds, loads, and its two unit suites pass, and its"
echo "         AWS-LC references match their registered version nodes."
echo ""
