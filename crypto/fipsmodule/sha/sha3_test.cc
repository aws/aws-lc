// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/evp.h>
#include <openssl/sha.h>

#include <gtest/gtest.h>

#include <openssl/digest.h>
#include "../../test/file_test.h"
#include "../../test/test_util.h"
#include "internal.h"


// SHA3TestVector corresponds to one test case of the NIST published file
// SHA3_256ShortMsg.txt.
// https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing
class SHA3TestVector {
 public:
  explicit SHA3TestVector() = default;
  ~SHA3TestVector() = default;

  bool ReadFromFileTest(FileTest *t);

  void NISTTestVectors(const EVP_MD *algorithm) const {
    uint32_t digest_length;
    std::unique_ptr<uint8_t[]> digest(new uint8_t[EVP_MD_size(algorithm)]);
    bssl::ScopedEVP_MD_CTX ctx;

    // Test the correctness via the Init, Update and Final Digest APIs.
    ASSERT_TRUE(EVP_DigestInit(ctx.get(), algorithm));
    ASSERT_TRUE(EVP_DigestUpdate(ctx.get(), msg_.data(), len_ / 8));
    ASSERT_TRUE(EVP_DigestFinal(ctx.get(), digest.get(), &digest_length));

    ASSERT_EQ(Bytes(digest.get(), EVP_MD_size(algorithm)),
              Bytes(digest_.data(), EVP_MD_size(algorithm)));
  }

  void NISTTestVectors_SingleShot(const EVP_MD *algorithm) const {
    uint32_t digest_length;
    std::unique_ptr<uint8_t[]> digest(new uint8_t[EVP_MD_size(algorithm)]);

    // Test the correctness via the Single-Shot EVP_Digest APIs.
    ASSERT_TRUE(EVP_Digest(msg_.data(), len_ / 8, digest.get(), &digest_length,
                           algorithm, nullptr));

    ASSERT_EQ(Bytes(digest.get(), EVP_MD_size(algorithm)),
              Bytes(digest_.data(), EVP_MD_size(algorithm)));
  }

  void NISTTestVectors_SHAKE(const EVP_MD *algorithm) const {
    uint32_t digest_length = out_len_ / 8;
    std::unique_ptr<uint8_t[]> digest(new uint8_t[digest_length]);
    bssl::ScopedEVP_MD_CTX ctx;

    // Test the incremental EVP API
    ASSERT_TRUE(EVP_DigestInit(ctx.get(), algorithm));
    ASSERT_TRUE(EVP_DigestUpdate(ctx.get(), msg_.data(), msg_.size()));
    ASSERT_TRUE(EVP_DigestFinalXOF(ctx.get(), digest.get(), digest_length));
    EXPECT_EQ(Bytes(digest.get(), digest_length),
              Bytes(digest_.data(), digest_length));

    // Test the one-shot
    ASSERT_TRUE(EVP_Digest(msg_.data(), msg_.size(), digest.get(),
                           &digest_length, algorithm, nullptr));
    EXPECT_EQ(Bytes(digest.get(), digest_length),
              Bytes(digest_.data(), digest_length));
  }

 private:
  uint32_t len_;
  uint32_t out_len_;
  std::vector<uint8_t> msg_;
  std::vector<uint8_t> digest_;
};

// Read the |key| attribute from |file_test| and convert it to an integer.
template <typename T>
bool FileTestReadInt(FileTest *file_test, T *out, const std::string &key) {
  std::string s;
  return file_test->GetAttribute(&s, key) &&
         testing::internal::ParseInt32(
             testing::Message() << "The value " << s.data()
                                << " is not convertable to an integer.",
             s.data(), (int *)out);
}

bool SHA3TestVector::ReadFromFileTest(FileTest *t) {
  if (t->HasAttribute("Outputlen")) {
    if (!FileTestReadInt(t, &out_len_, "Outputlen")) {
      return false;
    }
  }

  if (t->HasAttribute("Len")) {
    if (!FileTestReadInt(t, &len_, "Len")) {
      return false;
    }
  }

  if (!t->GetBytes(&msg_, "Msg") || !t->GetBytes(&digest_, "MD")) {
    return false;
  }

  return true;
}

TEST(SHA3Test, NISTTestVectors) {
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_224ShortMsg.txt",
                [](FileTest *t) {
                  SHA3TestVector test_vec;
                  EXPECT_TRUE(test_vec.ReadFromFileTest(t));
                  const EVP_MD *algorithm = EVP_sha3_224();
                  test_vec.NISTTestVectors(algorithm);
                });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_256ShortMsg.txt",
                [](FileTest *t) {
                  SHA3TestVector test_vec;
                  EXPECT_TRUE(test_vec.ReadFromFileTest(t));
                  const EVP_MD *algorithm = EVP_sha3_256();
                  test_vec.NISTTestVectors(algorithm);
                });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_384ShortMsg.txt",
                [](FileTest *t) {
                  SHA3TestVector test_vec;
                  EXPECT_TRUE(test_vec.ReadFromFileTest(t));
                  const EVP_MD *algorithm = EVP_sha3_384();
                  test_vec.NISTTestVectors(algorithm);
                });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_512ShortMsg.txt",
                [](FileTest *t) {
                  SHA3TestVector test_vec;
                  EXPECT_TRUE(test_vec.ReadFromFileTest(t));
                  const EVP_MD *algorithm = EVP_sha3_512();
                  test_vec.NISTTestVectors(algorithm);
                });
}

TEST(SHA3Test, NISTTestVectors_SingleShot) {
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_224ShortMsg.txt",
                [](FileTest *t) {
                  SHA3TestVector test_vec;
                  EXPECT_TRUE(test_vec.ReadFromFileTest(t));
                  const EVP_MD *algorithm = EVP_sha3_224();
                  test_vec.NISTTestVectors_SingleShot(algorithm);
                });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_256ShortMsg.txt",
                [](FileTest *t) {
                  SHA3TestVector test_vec;
                  EXPECT_TRUE(test_vec.ReadFromFileTest(t));
                  const EVP_MD *algorithm = EVP_sha3_256();
                  test_vec.NISTTestVectors_SingleShot(algorithm);
                });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_384ShortMsg.txt",
                [](FileTest *t) {
                  SHA3TestVector test_vec;
                  EXPECT_TRUE(test_vec.ReadFromFileTest(t));
                  const EVP_MD *algorithm = EVP_sha3_384();
                  test_vec.NISTTestVectors_SingleShot(algorithm);
                });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_512ShortMsg.txt",
                [](FileTest *t) {
                  SHA3TestVector test_vec;
                  EXPECT_TRUE(test_vec.ReadFromFileTest(t));
                  const EVP_MD *algorithm = EVP_sha3_512();
                  test_vec.NISTTestVectors_SingleShot(algorithm);
                });
}

TEST(KeccakInternalTest, SqueezeOutputBufferOverflow) {
  EVP_MD_unstable_sha3_enable(true);

  KECCAK1600_CTX ctx;
  std::vector<uint8_t> out;
  std::vector<uint8_t> canary(8);
  std::fill(canary.begin(), canary.end(), 0xff);

  const size_t out_lens[] = {
      0, 1, 2, 3, 4, 5, 6, 7, 8, (1 << 5), (1 << 16) + 1};
  for (auto out_len : out_lens) {
    EXPECT_TRUE(SHA3_Init(&ctx, SHA3_PAD_CHAR, SHA3_384_DIGEST_BITLENGTH));
    out.resize(out_len + canary.size());
    std::copy(canary.begin(), canary.end(), out.end() - canary.size());
    SHA3_Squeeze(ctx.A, out.data(), out_len, ctx.block_size);
    EXPECT_TRUE(std::equal(out.end() - canary.size(), out.end(),
                           canary.begin()) == true);
  }

  EVP_MD_unstable_sha3_enable(false);
}

TEST(SHAKETest, NISTTestVectors) {
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHAKE128VariableOut.txt",
                [](FileTest *t) {
                  SHA3TestVector test_vec;
                  EXPECT_TRUE(test_vec.ReadFromFileTest(t));
                  test_vec.NISTTestVectors_SHAKE(EVP_shake128());
                });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHAKE256VariableOut.txt",
                [](FileTest *t) {
                  SHA3TestVector test_vec;
                  EXPECT_TRUE(test_vec.ReadFromFileTest(t));
                  test_vec.NISTTestVectors_SHAKE(EVP_shake256());
                });
}
