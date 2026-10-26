// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/digest.h>

#include "backend/utils.h"
#include "boundary/utils.h"

namespace {

TEST(BackendDigestNamesTest, MatchesWithoutCase) {
  EXPECT_STREQ("SHA2-256", awslc_prov_digest_canonical_name("sha-256"));
}

TEST(BackendDigestNamesTest, RefusesNamesAwsLcLacks) {
  EXPECT_EQ(nullptr, awslc_prov_digest_canonical_name("SHA2-256/192"));
  EXPECT_EQ(nullptr, awslc_prov_digest_md("SHA2-256/192"));
}

}  // namespace
