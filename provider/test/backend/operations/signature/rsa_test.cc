// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/digest.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/rsa.h>

#include "backend/utils.h"
#include "boundary/utils.h"

namespace {

TEST(BackendSignatureTest, PinsReasonsTheFrontendSuiteMatches) {
  EXPECT_EQ(4, ERR_LIB_RSA);
  EXPECT_EQ(6, ERR_LIB_EVP);
  EXPECT_EQ(105, RSA_R_BAD_SIGNATURE);
  EXPECT_EQ(500, EVP_R_INVALID_PSS_MD);
}

// Every OpenSSL spelling reaches AWS-LC's digest, and nothing else does.
TEST(BackendSignatureTest, MapsOpenSslDigestNames) {
  for (const char *name :
       {"SHA2-256", "sha-256", "SHA256", "2.16.840.1.101.3.4.2.1"}) {
    SCOPED_TRACE(name);
    EXPECT_EQ(EVP_sha256(), awslc_prov_digest_md(name));
    EXPECT_STREQ("SHA2-256", awslc_prov_digest_canonical_name(name));
  }
  EXPECT_STREQ("SHA2-512/224", awslc_prov_digest_md_name(EVP_sha512_224()));

  // A prefix of an alias, a signature algorithm, and a digest AWS-LC lacks.
  for (const char *name : {"SHA2-25", "RSA-SHA256", "SHA2-256/192"}) {
    SCOPED_TRACE(name);
    EXPECT_EQ(nullptr, awslc_prov_digest_md(name));
    EXPECT_EQ(nullptr, awslc_prov_digest_canonical_name(name));
  }
}

}  // namespace
