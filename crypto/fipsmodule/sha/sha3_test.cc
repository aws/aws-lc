// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 

#include <openssl/evp.h>
#include <openssl/sha.h>

#include <gtest/gtest.h>

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
  
  void NISTTestVectors() const {
    uint32_t digest_length = SHA3_256_DIGEST_LENGTH;
    const EVP_MD* algorithm = EVP_sha3_256();
    uint8_t digest[SHA3_256_DIGEST_LENGTH];
    EVP_MD_CTX* ctx = EVP_MD_CTX_new();

    // SHA3 is disabled by default. First test this assumption and then enable SHA3 and test it!
    if (experimental_unstable_enable_sha3_get() == false){
      ASSERT_FALSE(EVP_DigestInit(ctx, algorithm));
      ASSERT_FALSE(EVP_DigestUpdate(ctx, msg_.data(), len_ / 8));
      ASSERT_FALSE(EVP_DigestFinal(ctx, digest, &digest_length));
    }

    // Enable SHA3
    experimental_unstable_enable_sha3_set(true);

    // Test the correctness via the Init, Update and Final Digest APIs.
    ASSERT_TRUE(EVP_DigestInit(ctx, algorithm));
    ASSERT_TRUE(EVP_DigestUpdate(ctx, msg_.data(), len_ / 8));
    ASSERT_TRUE(EVP_DigestFinal(ctx, digest, &digest_length));
    
    ASSERT_EQ(Bytes(digest, SHA3_256_DIGEST_LENGTH),
              Bytes(digest_.data(), SHA3_256_DIGEST_LENGTH));
    
    // Disable SHA3
    experimental_unstable_enable_sha3_set(false);

    // Test again SHA3 when |experimental_unstable_enable_sha3| is disabled
    ASSERT_FALSE(EVP_DigestInit(ctx, algorithm));
    ASSERT_FALSE(EVP_DigestUpdate(ctx, msg_.data(), len_ / 8));
    ASSERT_FALSE(EVP_DigestFinal(ctx, digest, &digest_length));

    OPENSSL_free(ctx);
  }

  void NISTTestVectors_SingleShot() const {
    uint32_t digest_length = SHA3_256_DIGEST_LENGTH;
    const EVP_MD* algorithm = EVP_sha3_256();
    uint8_t digest[SHA3_256_DIGEST_LENGTH];
    EVP_MD_CTX* ctx = EVP_MD_CTX_new();
    
    // SHA3 is disabled by default. First test this assumption and then enable SHA3 and test it!
    if (experimental_unstable_enable_sha3_get() == false) {
      ASSERT_FALSE(EVP_Digest(msg_.data(), len_ / 8, digest, &digest_length, algorithm, NULL));
    }

    // Enable SHA3
    experimental_unstable_enable_sha3_set(true);

    // Test the correctness via the Init, Update and Final Digest APIs.
    ASSERT_TRUE(EVP_Digest(msg_.data(), len_ / 8, digest, &digest_length, algorithm, NULL));
   
    ASSERT_EQ(Bytes(digest, SHA3_256_DIGEST_LENGTH),
              Bytes(digest_.data(), SHA3_256_DIGEST_LENGTH));

    // Disable SHA3
    experimental_unstable_enable_sha3_set(false);

    // Test again SHA3 when |experimental_unstable_enable_sha3| is disabled
    ASSERT_FALSE(EVP_Digest(msg_.data(), len_ / 8, digest, &digest_length, algorithm, NULL));
    
    OPENSSL_free(ctx);

  }

 private:
  uint16_t len_;
  std::vector<uint8_t> msg_;
  std::vector<uint8_t> digest_;
};

// Parses |s| as an unsigned integer of type T and writes the value to |out|.
// Returns true on success. If the integer value exceeds the maximum T value,
// returns false.
template <typename T>
bool ParseIntSafe(T *out, const std::string &s) {
  T value = 0;
  for (char c : s) {
    if (c < '0' || c > '9') {
      return false;
    }
    if (value > (std::numeric_limits<T>::max() - (c - '0')) / 10) {
      return false;
    }
    value = 10 * value + (c - '0');
  }
  *out = value;
  return true;
}

// Read the |key| attribute from |file_test| and convert it to an integer.
template <typename T>
bool FileTestReadInt(FileTest *file_test, T *out, const std::string &key) {
  std::string s;
  return file_test->GetAttribute(&s, key) && ParseIntSafe(out, s);
}

bool SHA3TestVector::ReadFromFileTest(FileTest *t) {
  if (!FileTestReadInt(t, &len_, "Len") ||
      !t->GetBytes(&msg_, "Msg") ||
      !t->GetBytes(&digest_, "MD")) {
    return false;
  }
  return true;
}

TEST(SHA3Test, NISTTestVectors) {
  FileTestGTest("crypto/fipsmodule/sha/SHA3_256ShortMsg.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    test_vec.NISTTestVectors();
  });
}

TEST(SHA3Test, NISTTestVectors_SingleShot) {
  FileTestGTest("crypto/fipsmodule/sha/SHA3_256ShortMsg.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    test_vec.NISTTestVectors_SingleShot();
  });
}
