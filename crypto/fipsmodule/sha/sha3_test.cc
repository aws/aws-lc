// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 

#include <openssl/evp.h>
#include <openssl/sha.h>

#include <gtest/gtest.h>

#include "../../test/file_test.h"
#include "../../test/test_util.h"
#include "internal.h"
#include <openssl/digest.h>


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

    #if !defined(OPENSSL_ANDROID)
    // SHA3 is disabled by default. First test this assumption and then enable SHA3 and test it.
    ASSERT_DEATH_IF_SUPPORTED(EVP_DigestInit(ctx, algorithm), "");
    ASSERT_DEATH_IF_SUPPORTED(EVP_DigestUpdate(ctx, msg_.data(), len_ / 8), "");
    ASSERT_DEATH_IF_SUPPORTED(EVP_DigestFinal(ctx, digest, &digest_length), "");
    #endif  // OPENSSL_ANDROID

    // Enable SHA3
    EVP_MD_unstable_sha3_enable(true);

    // Test the correctness via the Init, Update and Final Digest APIs.
    ASSERT_TRUE(EVP_DigestInit(ctx, algorithm));
    ASSERT_TRUE(EVP_DigestUpdate(ctx, msg_.data(), len_ / 8));
    ASSERT_TRUE(EVP_DigestFinal(ctx, digest, &digest_length));
    
    ASSERT_EQ(Bytes(digest, SHA3_256_DIGEST_LENGTH),
              Bytes(digest_.data(), SHA3_256_DIGEST_LENGTH));
 
    // Disable SHA3
    EVP_MD_unstable_sha3_enable(false);

    #if !defined(OPENSSL_ANDROID)
    // Test again SHA3 when |unstable_sha3_enabled_flag| is disabled.
    ASSERT_DEATH_IF_SUPPORTED(EVP_DigestInit(ctx, algorithm), "");
    ASSERT_DEATH_IF_SUPPORTED(EVP_DigestUpdate(ctx, msg_.data(), len_ / 8), "");
    ASSERT_DEATH_IF_SUPPORTED(EVP_DigestFinal(ctx, digest, &digest_length), "");
    #endif  // OPENSSL_ANDROID

    OPENSSL_free(ctx);
  }

  void NISTTestVectors_SingleShot() const {
    uint32_t digest_length = SHA3_256_DIGEST_LENGTH;
    const EVP_MD* algorithm = EVP_sha3_256();
    uint8_t digest[SHA3_256_DIGEST_LENGTH];
    EVP_MD_CTX* ctx = EVP_MD_CTX_new();
    
    #if !defined(OPENSSL_ANDROID)
    // SHA3 is disabled by default. First test this assumption and then enable SHA3 and test it.
    ASSERT_DEATH_IF_SUPPORTED(EVP_Digest(msg_.data(), len_ / 8, digest, &digest_length, algorithm, NULL), "");
    #endif  // OPENSSL_ANDROID

    // Enable SHA3
    EVP_MD_unstable_sha3_enable(true);

    // Test the correctness via the Single-Shot EVP_Digest APIs.
    ASSERT_TRUE(EVP_Digest(msg_.data(), len_ / 8, digest, &digest_length, algorithm, NULL));
   
    ASSERT_EQ(Bytes(digest, SHA3_256_DIGEST_LENGTH),
              Bytes(digest_.data(), SHA3_256_DIGEST_LENGTH));

    // Disable SHA3
    EVP_MD_unstable_sha3_enable(false);

    #if !defined(OPENSSL_ANDROID)
    // Test again SHA3 when |unstable_sha3_enabled_flag| is disabled.
    ASSERT_DEATH_IF_SUPPORTED(EVP_Digest(msg_.data(), len_ / 8, digest, &digest_length, algorithm, NULL), "");
    #endif  // OPENSSL_ANDROID
    
    OPENSSL_free(ctx);

  }

  void NISTTestVectors_SHAKE128() const {
    uint32_t digest_length = out_len_ / 8;
    uint8_t *digest = new uint8_t[digest_length];

    #if !defined(OPENSSL_ANDROID)
    ASSERT_DEATH_IF_SUPPORTED(SHAKE128(msg_.data(), msg_.size() , digest, out_len_), "");
    #endif  // OPENSSL_ANDROID

    // Enable SHA3
    EVP_MD_unstable_sha3_enable(true);
    
    ASSERT_TRUE(SHAKE128(msg_.data(), msg_.size() , digest, out_len_));
    
    ASSERT_EQ(Bytes(digest, out_len_ / 8),
            Bytes(digest_.data(), out_len_ / 8));

    // Disable SHA3
    EVP_MD_unstable_sha3_enable(false);

    #if !defined(OPENSSL_ANDROID)
    ASSERT_DEATH_IF_SUPPORTED(SHAKE128(msg_.data(), msg_.size() , digest, out_len_), "");
    #endif  // OPENSSL_ANDROID

    delete [] digest;
  }

  void NISTTestVectors_SHAKE256() const {
    uint32_t digest_length = out_len_ / 8;
    uint8_t *digest = new uint8_t[digest_length];

    #if !defined(OPENSSL_ANDROID)
    ASSERT_DEATH_IF_SUPPORTED(SHAKE256(msg_.data(), msg_.size() , digest, out_len_), "");
    #endif  // OPENSSL_ANDROID

    // Enable SHA3
    EVP_MD_unstable_sha3_enable(true);
    
    ASSERT_TRUE(SHAKE256(msg_.data(), msg_.size() , digest, out_len_));
    
    ASSERT_EQ(Bytes(digest, out_len_ / 8),
            Bytes(digest_.data(), out_len_ / 8));

    // Disable SHA3
    EVP_MD_unstable_sha3_enable(false);

    #if !defined(OPENSSL_ANDROID)
    ASSERT_DEATH_IF_SUPPORTED(SHAKE256(msg_.data(), msg_.size() , digest, out_len_), "");
    #endif  // OPENSSL_ANDROID

    delete [] digest;
  }

 private:
  uint16_t len_;
  uint16_t out_len_;
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
  if (!t->GetBytes(&msg_, "Msg") ||
      !t->GetBytes(&digest_, "MD")) {
    return false;
  }

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

TEST(SHAKE128Test, NISTTestVectors) {
  FileTestGTest("crypto/fipsmodule/sha/SHAKE128VariableOut.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    test_vec.NISTTestVectors_SHAKE128();
  });
}

TEST(SHAKE256Test, NISTTestVectors) {
  FileTestGTest("crypto/fipsmodule/sha/SHAKE256VariableOut.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    test_vec.NISTTestVectors_SHAKE256();
  });
}
