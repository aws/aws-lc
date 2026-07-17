// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <stdio.h>
#include <string.h>

#include <vector>

#include <gtest/gtest.h>

#include <openssl/digest.h>
#include <openssl/evp.h>
#include <openssl/span.h>

#include "internal.h"
#include "../fipsmodule/sha/internal.h"
#include "../internal.h"
#include "../test/file_test.h"
#include "../test/test_util.h"

// Keccak-256 (Ethereum-style, 0x01 padding) and FIPS SHA3-256 share rate and
// digest length but use different padding bytes, so their outputs must always
// differ. This guards against a future maintainer "fixing" the padding.
TEST(Keccak256Test, DiffersFromSHA3_256) {
  static_assert(KECCAK256_DIGEST_LENGTH == SHA3_256_DIGEST_LENGTH,
                "size mismatch invalidates compare");
  const char *kInputs[] = {"", "abc", "keccak", "hello world"};
  for (const char *in : kInputs) {
    SCOPED_TRACE(in);
    const size_t len = strlen(in);
    const uint8_t *data = reinterpret_cast<const uint8_t *>(in);
    uint8_t k[KECCAK256_DIGEST_LENGTH];
    uint8_t s[SHA3_256_DIGEST_LENGTH];
    ASSERT_EQ(k, Keccak256(data, len, k));
    ASSERT_EQ(s, SHA3_256(data, len, s));
    EXPECT_NE(0, OPENSSL_memcmp(k, s, KECCAK256_DIGEST_LENGTH))
        << "Keccak-256 and SHA3-256 must produce different digests";
  }
}

// File-driven Keccak-256 KAT vectors. Format mirrors NIST SHA-3 KATs
// (Len in bits, Msg/MD in lowercase hex). See sha3_test.cc for the same
// pattern applied to SHA-3.
TEST(Keccak256Test, KAT) {
  auto run = [](FileTest *t) {
    std::string len_str;
    ASSERT_TRUE(t->GetAttribute(&len_str, "Len"));
    int bit_len = 0;
    ASSERT_EQ(1, sscanf(len_str.c_str(), "%d", &bit_len));
    ASSERT_GE(bit_len, 0);
    // The current KAT covers byte-aligned messages only; bit-level inputs
    // need a separate API.
    ASSERT_EQ(0, bit_len % 8) << "Non-byte-aligned KAT vectors are unsupported";
    const size_t byte_len = static_cast<size_t>(bit_len) / 8;

    std::vector<uint8_t> msg, md;
    ASSERT_TRUE(t->GetBytes(&msg, "Msg"));
    ASSERT_TRUE(t->GetBytes(&md, "MD"));
    ASSERT_LE(byte_len, msg.size());
    ASSERT_EQ(static_cast<size_t>(KECCAK256_DIGEST_LENGTH), md.size());

    uint8_t out[KECCAK256_DIGEST_LENGTH];
    ASSERT_EQ(out, Keccak256(msg.data(), byte_len, out));
    EXPECT_EQ(EncodeHex(bssl::MakeConstSpan(md)),
              EncodeHex(bssl::MakeConstSpan(out, KECCAK256_DIGEST_LENGTH)));

    // Drive the streaming EVP path one byte at a time to exercise the
    // partial-block buffering in Keccak256_Update, and confirm it matches the
    // one-shot. This goes through the same public entry point external callers
    // use (the streaming Keccak256_* primitives are not exported directly).
    bssl::ScopedEVP_MD_CTX ctx;
    ASSERT_TRUE(EVP_DigestInit_ex(ctx.get(), EVP_keccak256(), nullptr));
    for (size_t i = 0; i < byte_len; i++) {
      ASSERT_TRUE(EVP_DigestUpdate(ctx.get(), &msg[i], 1));
    }
    unsigned out_len = 0;
    OPENSSL_memset(out, 0, sizeof(out));
    ASSERT_TRUE(EVP_DigestFinal_ex(ctx.get(), out, &out_len));
    ASSERT_EQ(static_cast<unsigned>(KECCAK256_DIGEST_LENGTH), out_len);
    EXPECT_EQ(EncodeHex(bssl::MakeConstSpan(md)),
              EncodeHex(bssl::MakeConstSpan(out, KECCAK256_DIGEST_LENGTH)));
  };
  FileTestGTest("crypto/keccak/testvectors/KECCAK256ShortMsg.txt", run);
  FileTestGTest("crypto/keccak/testvectors/KECCAK256LongMsg.txt", run);
}
