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
  
  void NISTTestVectors(const EVP_MD *algorithm) const {
    uint32_t digest_length;
    std::unique_ptr<uint8_t[]> digest(new uint8_t[EVP_MD_size(algorithm)]);
    EVP_MD_CTX* ctx = EVP_MD_CTX_new();

    // SHA3 is disabled by default. First test this assumption and then enable SHA3 and test it.
    ASSERT_FALSE(EVP_DigestInit(ctx, algorithm));
    ASSERT_FALSE(EVP_DigestUpdate(ctx, msg_.data(), len_ / 8));
    ASSERT_FALSE(EVP_DigestFinal(ctx, digest.get(), &digest_length));

    // Enable SHA3
    EVP_MD_unstable_sha3_enable(true);

    // Test the correctness via the Init, Update and Final Digest APIs.
    ASSERT_TRUE(EVP_DigestInit(ctx, algorithm));
    ASSERT_TRUE(EVP_DigestUpdate(ctx, msg_.data(), len_ / 8));
    ASSERT_TRUE(EVP_DigestFinal(ctx, digest.get(), &digest_length));
    
    ASSERT_EQ(Bytes(digest.get(), EVP_MD_size(algorithm)),
              Bytes(digest_.data(), EVP_MD_size(algorithm)));
 
    // Disable SHA3
    EVP_MD_unstable_sha3_enable(false);

    // Test again SHA3 when |unstable_sha3_enabled_flag| is disabled.
    ASSERT_FALSE(EVP_DigestInit(ctx, algorithm));
    ASSERT_FALSE(EVP_DigestUpdate(ctx, msg_.data(), len_ / 8));
    ASSERT_FALSE(EVP_DigestFinal(ctx, digest.get(), &digest_length));

    OPENSSL_free(ctx);
  }

  void NISTTestVectors_SingleShot(const EVP_MD *algorithm) const {
    uint32_t digest_length;
    std::unique_ptr<uint8_t[]> digest(new uint8_t[EVP_MD_size(algorithm)]);
    EVP_MD_CTX* ctx = EVP_MD_CTX_new();
    
    // SHA3 is disabled by default. First test this assumption and then enable SHA3 and test it.
    ASSERT_FALSE(EVP_Digest(msg_.data(), len_ / 8, digest.get(), &digest_length, algorithm, NULL));

    // Enable SHA3
    EVP_MD_unstable_sha3_enable(true);

    // Test the correctness via the Single-Shot EVP_Digest APIs.
    ASSERT_TRUE(EVP_Digest(msg_.data(), len_ / 8, digest.get(), &digest_length, algorithm, NULL));
   
    ASSERT_EQ(Bytes(digest.get(), EVP_MD_size(algorithm)),
              Bytes(digest_.data(), EVP_MD_size(algorithm)));

    // Disable SHA3
    EVP_MD_unstable_sha3_enable(false);

    // Test again SHA3 when |unstable_sha3_enabled_flag| is disabled.
    ASSERT_FALSE(EVP_Digest(msg_.data(), len_ / 8, digest.get(), &digest_length, algorithm, NULL));

    OPENSSL_free(ctx);
  }

  void NISTTestVectors_SHAKE128() const {
    uint32_t digest_length = out_len_ / 8;
    std::unique_ptr<uint8_t[]> digest(new uint8_t[digest_length]);

    ASSERT_FALSE(SHAKE128(msg_.data(), msg_.size() , digest.get(), out_len_));

    // Enable SHA3
    EVP_MD_unstable_sha3_enable(true);
    
    ASSERT_TRUE(SHAKE128(msg_.data(), msg_.size() , digest.get(), out_len_));
    
    ASSERT_EQ(Bytes(digest.get(), out_len_ / 8),
            Bytes(digest_.data(), out_len_ / 8));

    // Disable SHA3
    EVP_MD_unstable_sha3_enable(false);

    ASSERT_FALSE(SHAKE128(msg_.data(), msg_.size() , digest.get(), out_len_));
  }

  void NISTTestVectors_SHAKE256() const {
    uint32_t digest_length = out_len_ / 8;
    std::unique_ptr<uint8_t[]> digest(new uint8_t[digest_length]);

    ASSERT_FALSE(SHAKE256(msg_.data(), msg_.size() , digest.get(), out_len_));

    // Enable SHA3
    EVP_MD_unstable_sha3_enable(true);
    
    ASSERT_TRUE(SHAKE256(msg_.data(), msg_.size() , digest.get(), out_len_));
    
    ASSERT_EQ(Bytes(digest.get(), out_len_ / 8),
            Bytes(digest_.data(), out_len_ / 8));

    // Disable SHA3
    EVP_MD_unstable_sha3_enable(false);

    ASSERT_FALSE(SHAKE256(msg_.data(), msg_.size() , digest.get(), out_len_));
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
  testing::internal::ParseInt32(testing::Message() << "The value " << s.data() << \
  " is not convertable to an integer.", s.data(), (int *) out);
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
  
  if (!t->GetBytes(&msg_, "Msg") ||
      !t->GetBytes(&digest_, "MD")) {
    return false;
  }

  return true;
}

TEST(SHA3Test, NISTTestVectors) {
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_224ShortMsg.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    const EVP_MD* algorithm = EVP_sha3_224();
    test_vec.NISTTestVectors(algorithm);
  });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_256ShortMsg.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    const EVP_MD* algorithm = EVP_sha3_256();
    test_vec.NISTTestVectors(algorithm);
  });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_384ShortMsg.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    const EVP_MD* algorithm = EVP_sha3_384();
    test_vec.NISTTestVectors(algorithm);
  });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_512ShortMsg.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    const EVP_MD* algorithm = EVP_sha3_512();
    test_vec.NISTTestVectors(algorithm);
  });
}

TEST(SHA3Test, NISTTestVectors_SingleShot) {
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_224ShortMsg.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    const EVP_MD* algorithm = EVP_sha3_224();
    test_vec.NISTTestVectors_SingleShot(algorithm);
  });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_256ShortMsg.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    const EVP_MD* algorithm = EVP_sha3_256();
    test_vec.NISTTestVectors_SingleShot(algorithm);
  });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_384ShortMsg.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    const EVP_MD* algorithm = EVP_sha3_384();
    test_vec.NISTTestVectors_SingleShot(algorithm);
  });
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHA3_512ShortMsg.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    const EVP_MD* algorithm = EVP_sha3_512();
    test_vec.NISTTestVectors_SingleShot(algorithm);
  });
}

TEST(SHAKE128Test, NISTTestVectors) {
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHAKE128VariableOut.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    test_vec.NISTTestVectors_SHAKE128();
  });
}

TEST(SHAKE256Test, NISTTestVectors) {
  FileTestGTest("crypto/fipsmodule/sha/testvectors/SHAKE256VariableOut.txt", [](FileTest *t) {
    SHA3TestVector test_vec;
    EXPECT_TRUE(test_vec.ReadFromFileTest(t));
    test_vec.NISTTestVectors_SHAKE256();
  });
}
