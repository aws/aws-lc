// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// The back side enforces output bounds that AWS-LC's size-less SHA*_Final
// functions cannot enforce themselves. OpenSSL's EVP layer always supplies the
// advertised digest size, so this guarantee must be tested directly here.

#include <gtest/gtest.h>

#include <stddef.h>

#include <vector>

#include "internal/backend/digests.h"

namespace {

const std::vector<unsigned char> kSha256Abc = {
    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40,
    0xde, 0x5d, 0xae, 0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17,
    0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad};

// One row per algorithm the back side wraps.
struct BackendDigest {
  const char *name;
  size_t (*ctx_size)(void);
  size_t (*digest_size)(void);
  int (*init)(void *ctx);
  int (*update)(void *ctx, const void *data, size_t len);
  int (*final)(void *ctx, unsigned char *out, size_t out_size);
  const std::vector<unsigned char> *expected;
};

const BackendDigest kBackendDigests[] = {
    {"SHA-256", awslc_prov_sha256_ctx_size, awslc_prov_sha256_digest_size,
     awslc_prov_sha256_init, awslc_prov_sha256_update,
     awslc_prov_sha256_final, &kSha256Abc},
};

class BackendDigestTest : public testing::TestWithParam<BackendDigest> {};

TEST_P(BackendDigestTest, RejectsUndersizedOutputWithoutWriting) {
  const BackendDigest &d = GetParam();
  const unsigned char kCanary = 0xa5;
  const char kInput[] = "abc";
  std::vector<unsigned char> ctx(d.ctx_size(), 0);
  std::vector<unsigned char> output(d.digest_size(), kCanary);

  ASSERT_FALSE(ctx.empty());
  ASSERT_FALSE(output.empty());
  ASSERT_TRUE(d.init(ctx.data()));
  ASSERT_TRUE(d.update(ctx.data(), kInput, sizeof(kInput) - 1));

  // The allocation is deliberately large enough to keep a broken implementation
  // from causing undefined behavior. Only the reported size is short, and the
  // canary proves the size-less AWS-LC final function was never called.
  ASSERT_FALSE(d.final(ctx.data(), output.data(), output.size() - 1));
  for (unsigned char byte : output) {
    EXPECT_EQ(kCanary, byte);
  }

  // Rejection happens before AWS-LC sees the context, so the same operation can
  // still be finalized into a correctly sized buffer.
  ASSERT_TRUE(d.final(ctx.data(), output.data(), output.size()));
  EXPECT_EQ(*d.expected, output);
}

INSTANTIATE_TEST_SUITE_P(Digests, BackendDigestTest,
                         testing::ValuesIn(kBackendDigests),
                         [](const testing::TestParamInfo<BackendDigest> &info) {
                           std::string name = info.param.name;
                           for (char &c : name) {
                             if (c == '-' || c == '/') {
                               c = '_';
                             }
                           }
                           return name;
                         });

}  // namespace
