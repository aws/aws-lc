#!/usr/bin/env bash
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC

set -exo pipefail

source tests/ci/common_posix_setup.sh

# Neutralize automatic seeding for the general test suite. With
# -DENABLE_CRYPTO_POLICIES=ON every SSL_CTX_new is seeded from the system policy
# on a host that renders one; the thousands of existing ssl tests assume AWS-LC's
# built-in defaults and are not written for that. Pointing
# AWSLC_CRYPTO_POLICY_FILE at a path that does not exist makes seeding a no-op
# for the bulk suite, verifying the flag-on build does not regress existing
# tests.
#
# The dedicated CryptoPolicyTest cases manage their own policy files/paths and
# still exercise seeding; the system policy itself is covered by the run below.
export AWSLC_CRYPTO_POLICY_FILE=/nonexistent/aws-lc-crypto-policy-disabled

echo "Testing AWS-LC with crypto-policies support (stock configuration)."
build_and_test -DENABLE_CRYPTO_POLICIES=ON

echo "Testing AWS-LC with crypto-policies support (stock configuration, release)."
build_and_test -DENABLE_CRYPTO_POLICIES=ON -DCMAKE_BUILD_TYPE=Release

# The release tree is still on disk, so re-run just the crypto-policies tests
# against a file crypto-policies itself renders, rather than a fixture the tests
# wrote. The image's crypto-policies has no AWS-LC generator and so renders no
# aws-lc.config, the default path; this run names the OpenSSL back-end, which
# carries the same directives in OpenSSL's spellings.
# AWSLC_CRYPTO_POLICY_TEST_REQUIRE_SYSTEM makes an absent file a failure, since
# this job runs only on Amazon Linux 2023, which ships that back-end.
echo "Testing crypto-policies seeding against the system policy."
cat /etc/crypto-policies/config \
    /etc/crypto-policies/back-ends/opensslcnf.config \
    || echo "no crypto-policies installation found"
env AWSLC_CRYPTO_POLICY_FILE=/etc/crypto-policies/back-ends/opensslcnf.config \
    AWSLC_CRYPTO_POLICY_TEST_REQUIRE_SYSTEM=1 \
    "${BUILD_ROOT}/ssl/ssl_test" --gtest_filter='CryptoPolicy*'

# Distributions package AWS-LC shared with symbol versioning, where the policy
# reader reaches ssl_test only through OPENSSL_EXPORT and its ssl/libssl.txt
# entries. A static build proves neither gate.
echo "Testing AWS-LC with crypto-policies support (distribution configuration)."
build_and_test -DENABLE_CRYPTO_POLICIES=ON -DBUILD_SHARED_LIBS=ON \
    -DENABLE_DIST_PKG=ON -DENABLE_SYMBOL_VERSIONING=ON -DCMAKE_BUILD_TYPE=Release

# Sanity: enabling the flag must not break a libssl-off build. crypto_policy.cc
# lives only in libssl, so it should simply not be compiled.
echo "Testing crypto-policies flag with libssl OFF."
build_and_test -DENABLE_CRYPTO_POLICIES=ON -DBUILD_LIBSSL=OFF -DCMAKE_BUILD_TYPE=Release
