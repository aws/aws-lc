#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

# Neutralize automatic seeding for the general test suite. On Amazon Linux 2023 /
# Fedora the real /etc/crypto-policies/back-ends/opensslcnf.config exists, so with
# -DENABLE_CRYPTO_POLICIES=ON every SSL_CTX_new would otherwise be seeded from the
# system policy; the thousands of existing ssl tests assume AWS-LC's built-in
# defaults and are not written for that. Pointing AWSLC_CRYPTO_POLICY_FILE at a
# path that does not exist makes seeding a no-op for the bulk suite, verifying the
# flag-on build does not regress existing tests.
#
# The dedicated CryptoPolicyTest cases manage their own policy files/paths and
# still exercise seeding. In particular CryptoPolicyTest.SystemPolicyIfPresent
# temporarily clears this variable to read the real system policy file, so the
# feature is still validated end-to-end on Amazon Linux 2023 (and skips
# elsewhere).
export AWSLC_CRYPTO_POLICY_FILE=/nonexistent/aws-lc-crypto-policy-disabled

echo "Testing AWS-LC with crypto-policies seeding (debug)."
build_and_test -DENABLE_CRYPTO_POLICIES=ON

echo "Testing AWS-LC with crypto-policies seeding (release)."
build_and_test -DENABLE_CRYPTO_POLICIES=ON -DCMAKE_BUILD_TYPE=Release

# Sanity: enabling the flag must not break a libssl-off build. crypto_policy.cc
# lives only in libssl, so it should simply not be compiled.
echo "Testing crypto-policies flag with libssl OFF."
build_and_test -DENABLE_CRYPTO_POLICIES=ON -DBUILD_LIBSSL=OFF -DCMAKE_BUILD_TYPE=Release
