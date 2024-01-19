/* Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com)
 * All rights reserved.
 *
 * This package is an SSL implementation written
 * by Eric Young (eay@cryptsoft.com).
 * The implementation was written so as to conform with Netscapes SSL.
 *
 * This library is free for commercial and non-commercial use as long as
 * the following conditions are aheared to.  The following conditions
 * apply to all code found in this distribution, be it the RC4, RSA,
 * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
 * included with this distribution is covered by the same copyright terms
 * except that the holder is Tim Hudson (tjh@cryptsoft.com).
 *
 * Copyright remains Eric Young's, and as such any Copyright notices in
 * the code are not to be removed.
 * If this package is used in a product, Eric Young should be given attribution
 * as the author of the parts of the library used.
 * This can be in the form of a textual message at program startup or
 * in documentation (online or textual) provided with the package.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.] */

#include <memory>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include <openssl/digest.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>

#include "../test/file_test.h"
#include "../test/test_util.h"
#include "../test/wycheproof_util.h"


static const EVP_MD *GetDigest(const std::string &name) {
  if (name == "MD5") {
    return EVP_md5();
  } else if (name == "SHA1") {
    return EVP_sha1();
  } else if (name == "SHA224") {
    return EVP_sha224();
  } else if (name == "SHA256") {
    return EVP_sha256();
  } else if (name == "SHA384") {
    return EVP_sha384();
  } else if (name == "SHA512") {
    return EVP_sha512();
  } else if (name == "SHA512/224") {
    return EVP_sha512_224();
  } else if (name == "SHA512/256") {
    return EVP_sha512_256();
  }
  return nullptr;
}

static void RunHMACTestEVP(const std::vector<uint8_t> &key,
                           const std::vector<uint8_t> &msg,
                           const std::vector<uint8_t> &tag, const EVP_MD *md) {
  bssl::UniquePtr<EVP_PKEY> pkey(
      EVP_PKEY_new_mac_key(EVP_PKEY_HMAC, nullptr, key.data(), key.size()));
  ASSERT_TRUE(pkey);

  bssl::ScopedEVP_MD_CTX copy, mctx;
  size_t len;
  std::vector<uint8_t> actual;
  ASSERT_TRUE(EVP_DigestSignInit(mctx.get(), nullptr, md, nullptr, pkey.get()));
  // Make a copy we can test against later.
  ASSERT_TRUE(EVP_MD_CTX_copy_ex(copy.get(), mctx.get()));
  ASSERT_TRUE(EVP_DigestSignUpdate(mctx.get(), msg.data(), msg.size()));
  ASSERT_TRUE(EVP_DigestSignFinal(mctx.get(), nullptr, &len));
  actual.resize(len);
  ASSERT_TRUE(EVP_DigestSignFinal(mctx.get(), actual.data(), &len));
  actual.resize(len);
  // Wycheproof tests truncate the tags down to |tagSize|. Expected outputs in
  // hmac_tests.txt have the length of the entire tag.
  EXPECT_EQ(Bytes(tag), Bytes(actual.data(), tag.size()));

  // Repeat the test with |copy|, to check |EVP_MD_CTX_copy_ex| duplicated
  // everything.
  len = 0;
  actual.clear();
  ASSERT_TRUE(EVP_DigestSignUpdate(copy.get(), msg.data(), msg.size()));
  ASSERT_TRUE(EVP_DigestSignFinal(copy.get(), nullptr, &len));
  actual.resize(len);
  ASSERT_TRUE(EVP_DigestSignFinal(copy.get(), actual.data(), &len));
  actual.resize(len);
  EXPECT_EQ(Bytes(tag), Bytes(actual.data(), tag.size()));

  // Test using the one-shot API.
  mctx.Reset();
  copy.Reset();
  len = 0;
  actual.clear();
  ASSERT_TRUE(EVP_DigestSignInit(mctx.get(), nullptr, md, nullptr, pkey.get()));
  ASSERT_TRUE(EVP_MD_CTX_copy_ex(copy.get(), mctx.get()));
  ASSERT_TRUE(
      EVP_DigestSign(mctx.get(), nullptr, &len, msg.data(), msg.size()));
  actual.resize(len);
  ASSERT_TRUE(
      EVP_DigestSign(mctx.get(), actual.data(), &len, msg.data(), msg.size()));
  actual.resize(len);
  EXPECT_EQ(Bytes(tag), Bytes(actual.data(), tag.size()));

  // Repeat the test with |copy|, to check |EVP_MD_CTX_copy_ex| duplicated
  // everything.
  len = 0;
  actual.clear();
  ASSERT_TRUE(EVP_DigestSignUpdate(copy.get(), msg.data(), msg.size()));
  ASSERT_TRUE(EVP_DigestSignFinal(copy.get(), nullptr, &len));
  actual.resize(len);
  ASSERT_TRUE(EVP_DigestSignFinal(copy.get(), actual.data(), &len));
  actual.resize(len);
  EXPECT_EQ(Bytes(tag), Bytes(actual.data(), tag.size()));

  // Test feeding the input in byte by byte.
  mctx.Reset();
  ASSERT_TRUE(EVP_DigestSignInit(mctx.get(), nullptr, md, nullptr, pkey.get()));
  for (const unsigned char &i : msg) {
    ASSERT_TRUE(EVP_DigestSignUpdate(mctx.get(), &i, 1));
  }
  ASSERT_TRUE(EVP_DigestSignFinal(mctx.get(), actual.data(), &len));
  EXPECT_EQ(Bytes(tag), Bytes(actual.data(), tag.size()));


  // Test |EVP_PKEY| key creation with |EVP_PKEY_new_raw_private_key|.
  bssl::UniquePtr<EVP_PKEY> raw_pkey(EVP_PKEY_new_raw_private_key(
      EVP_PKEY_HMAC, nullptr, key.data(), key.size()));
  mctx.Reset();
  len = 0;
  actual.clear();
  EXPECT_TRUE(
      EVP_DigestSignInit(mctx.get(), nullptr, md, nullptr, raw_pkey.get()));
  EXPECT_TRUE(EVP_DigestSignUpdate(mctx.get(), msg.data(), msg.size()));
  EXPECT_TRUE(EVP_DigestSignFinal(mctx.get(), nullptr, &len));
  actual.resize(len);
  EXPECT_TRUE(EVP_DigestSignFinal(mctx.get(), actual.data(), &len));
  actual.resize(len);
  EXPECT_EQ(Bytes(tag), Bytes(actual.data(), tag.size()));

  // Test retrieving key passed into |raw_pkey| with
  // |EVP_PKEY_get_raw_private_key|.
  std::vector<uint8_t> retrieved_key;
  size_t retrieved_key_len;
  EXPECT_TRUE(EVP_PKEY_get_raw_private_key(raw_pkey.get(), nullptr,
                                           &retrieved_key_len));
  EXPECT_EQ(key.size(), retrieved_key_len);
  retrieved_key.resize(retrieved_key_len);
  EXPECT_TRUE(EVP_PKEY_get_raw_private_key(raw_pkey.get(), retrieved_key.data(),
                                           &retrieved_key_len));
  retrieved_key.resize(retrieved_key_len);
  EXPECT_EQ(Bytes(retrieved_key), Bytes(key));

  // Test retrieving key with a buffer length that's too small. This should fail
  if (!key.empty()) {
    size_t short_key_len = retrieved_key_len - 1;
    EXPECT_FALSE(EVP_PKEY_get_raw_private_key(
        raw_pkey.get(), retrieved_key.data(), &short_key_len));
  }
}


TEST(HMACTest, TestVectors) {
  FileTestGTest("crypto/hmac_extra/hmac_tests.txt", [](FileTest *t) {
    std::string digest_str;
    ASSERT_TRUE(t->GetAttribute(&digest_str, "HMAC"));
    const EVP_MD *digest = GetDigest(digest_str);
    ASSERT_TRUE(digest) << "Unknown digest: " << digest_str;

    std::vector<uint8_t> key, input, output;
    ASSERT_TRUE(t->GetBytes(&key, "Key"));
    ASSERT_TRUE(t->GetBytes(&input, "Input"));
    ASSERT_TRUE(t->GetBytes(&output, "Output"));
    ASSERT_EQ(EVP_MD_size(digest), output.size());

    // Test using the one-shot API.
    unsigned expected_mac_len = EVP_MD_size(digest);
    std::unique_ptr<uint8_t[]> mac(new uint8_t[expected_mac_len]);
    unsigned mac_len;
    ASSERT_TRUE(HMAC(digest, key.data(), key.size(), input.data(), input.size(),
                     mac.get(), &mac_len));
    EXPECT_EQ(Bytes(output), Bytes(mac.get(), mac_len));
    OPENSSL_memset(mac.get(), 0, expected_mac_len); // Clear the prior correct answer

    // Test using HMAC_CTX.
    bssl::ScopedHMAC_CTX ctx;
    ASSERT_TRUE(
        HMAC_Init_ex(ctx.get(), key.data(), key.size(), digest, nullptr));
    ASSERT_TRUE(HMAC_Update(ctx.get(), input.data(), input.size()));
    ASSERT_TRUE(HMAC_Final(ctx.get(), mac.get(), &mac_len));
    EXPECT_EQ(Bytes(output), Bytes(mac.get(), mac_len));
    OPENSSL_memset(mac.get(), 0, expected_mac_len); // Clear the prior correct answer

    // Test that an HMAC_CTX may be reset with the same key.
    ASSERT_TRUE(HMAC_Init_ex(ctx.get(), nullptr, 0, digest, nullptr));
    ASSERT_TRUE(HMAC_Update(ctx.get(), input.data(), input.size()));
    ASSERT_TRUE(HMAC_Final(ctx.get(), mac.get(), &mac_len));
    EXPECT_EQ(Bytes(output), Bytes(mac.get(), mac_len));
    OPENSSL_memset(mac.get(), 0, expected_mac_len); // Clear the prior correct answer

    // Test that an HMAC_CTX may be reset with the same key and an null md
    ASSERT_TRUE(HMAC_Init_ex(ctx.get(), nullptr, 0, nullptr, nullptr));
    ASSERT_TRUE(HMAC_Update(ctx.get(), input.data(), input.size()));
    ASSERT_TRUE(HMAC_Final(ctx.get(), mac.get(), &mac_len));
    EXPECT_EQ(Bytes(output), Bytes(mac.get(), mac_len));
    OPENSSL_memset(mac.get(), 0, expected_mac_len);  // Clear the prior correct answer

    // Some callers will call init multiple times and we need to ensure that doesn't break anything
    ASSERT_TRUE(HMAC_Init_ex(ctx.get(), key.data(), key.size(), digest, nullptr));
    ASSERT_TRUE(HMAC_Init_ex(ctx.get(), nullptr, 0, nullptr, nullptr));
    ASSERT_TRUE(HMAC_Update(ctx.get(), input.data(), input.size()));
    ASSERT_TRUE(HMAC_Final(ctx.get(), mac.get(), &mac_len));
    EXPECT_EQ(Bytes(output), Bytes(mac.get(), mac_len));
    OPENSSL_memset(mac.get(), 0, expected_mac_len);  // Clear the prior correct answer

    // Test feeding the input in byte by byte.
    ASSERT_TRUE(HMAC_Init_ex(ctx.get(), nullptr, 0, nullptr, nullptr));
    for (size_t i = 0; i < input.size(); i++) {
      ASSERT_TRUE(HMAC_Update(ctx.get(), &input[i], 1));
    }
    ASSERT_TRUE(HMAC_Final(ctx.get(), mac.get(), &mac_len));
    EXPECT_EQ(Bytes(output), Bytes(mac.get(), mac_len));

    // Test consuming HMAC through the |EVP_PKEY_HMAC| interface.
    RunHMACTestEVP(key, input, output, digest);
  });
}

static void RunWycheproofTest(const char *path, const EVP_MD *md) {
  SCOPED_TRACE(path);
  FileTestGTest(path, [&](FileTest *t) {
    t->IgnoreInstruction("keySize");
    t->IgnoreInstruction("tagSize");
    std::vector<uint8_t> key, msg, tag;
    ASSERT_TRUE(t->GetBytes(&key, "key"));
    ASSERT_TRUE(t->GetBytes(&msg, "msg"));
    ASSERT_TRUE(t->GetBytes(&tag, "tag"));
    WycheproofResult result;
    ASSERT_TRUE(GetWycheproofResult(t, &result));

    if (!result.IsValid()) {
      // Wycheproof tests assume the HMAC implementation checks the MAC. Ours
      // simply computes the HMAC, so skip the tests with invalid outputs.
      return;
    }

    uint8_t out[EVP_MAX_MD_SIZE];
    unsigned out_len;
    ASSERT_TRUE(HMAC(md, key.data(), key.size(), msg.data(), msg.size(), out,
                     &out_len));
    // Wycheproof tests truncate the tags down to |tagSize|.
    ASSERT_LE(tag.size(), out_len);
    EXPECT_EQ(Bytes(out, tag.size()), Bytes(tag));

    // Run Wycheproof tests through the |EVP_PKEY_HMAC| interface.
    RunHMACTestEVP(key, msg, tag, md);
  });
}

TEST(HMACTest, WycheproofSHA1) {
  RunWycheproofTest("third_party/wycheproof_testvectors/hmac_sha1_test.txt",
                    EVP_sha1());
}

TEST(HMACTest, WycheproofSHA224) {
  RunWycheproofTest("third_party/wycheproof_testvectors/hmac_sha224_test.txt",
                    EVP_sha224());
}

TEST(HMACTest, WycheproofSHA256) {
  RunWycheproofTest("third_party/wycheproof_testvectors/hmac_sha256_test.txt",
                    EVP_sha256());
}

TEST(HMACTest, WycheproofSHA384) {
  RunWycheproofTest("third_party/wycheproof_testvectors/hmac_sha384_test.txt",
                    EVP_sha384());
}

TEST(HMACTest, WycheproofSHA512) {
  RunWycheproofTest("third_party/wycheproof_testvectors/hmac_sha512_test.txt",
                    EVP_sha512());
}

TEST(HMACTest, WycheproofSHA512_224) {
  RunWycheproofTest("third_party/wycheproof_testvectors/hmac_sha512_224_test.txt",
                    EVP_sha512_224());
}

TEST(HMACTest, WycheproofSHA512_256) {
  RunWycheproofTest("third_party/wycheproof_testvectors/hmac_sha512_256_test.txt",
                    EVP_sha512_256());
}

TEST(HMACTest, EVP_DigestVerify) {
  bssl::UniquePtr<EVP_PKEY> pkey(
      EVP_PKEY_new_mac_key(EVP_PKEY_HMAC, nullptr, nullptr, 0));
  ASSERT_TRUE(pkey);

  bssl::ScopedEVP_MD_CTX mctx;
  EXPECT_FALSE(EVP_DigestVerifyInit(mctx.get(), nullptr, EVP_sha256(), nullptr,
                                    pkey.get()));
  EXPECT_EQ(EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE,
            ERR_GET_REASON(ERR_get_error()));

  EXPECT_FALSE(EVP_DigestVerifyUpdate(mctx.get(), nullptr, 0));
  EXPECT_EQ(EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE,
            ERR_GET_REASON(ERR_get_error()));

  EXPECT_FALSE(EVP_DigestVerifyFinal(mctx.get(), nullptr, 0));
  EXPECT_EQ(EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE,
            ERR_GET_REASON(ERR_get_error()));

  EXPECT_FALSE(EVP_DigestVerify(mctx.get(), nullptr, 0, nullptr, 0));
  EXPECT_EQ(EVP_R_OPERATION_NOT_SUPPORTED_FOR_THIS_KEYTYPE,
            ERR_GET_REASON(ERR_get_error()));
}
