/* Copyright (c) 2018, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. 
 */

#include <openssl/evp.h>
#include <openssl/sha.h>

#include <gtest/gtest.h>

#include "../../test/test_util.h"
#include "../../test/file_test.h"
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

    ASSERT_TRUE(EVP_DigestInit(ctx, algorithm));
    ASSERT_TRUE(EVP_DigestUpdate(ctx, msg_.data(), len_ / 8));
    ASSERT_TRUE(EVP_DigestFinal(ctx, digest, &digest_length));
   
    ASSERT_EQ(Bytes(digest, SHA3_256_DIGEST_LENGTH),
              Bytes(digest_.data(), SHA3_256_DIGEST_LENGTH));
    
    OPENSSL_cleanse(ctx, sizeof(EVP_MD_CTX));
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
