// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/x509.h"
#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "internal.h"
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <streambuf>
#include <cerrno>

#ifdef _WIN32
#include <windows.h>
#ifndef PATH_MAX
#define PATH_MAX MAX_PATH
#endif
#else
#include <unistd.h>
#ifndef PATH_MAX
#define PATH_MAX 4096
#endif
#endif

size_t createTempFILEpath(char buffer[PATH_MAX]);
void RemoveFile(const char* path);

X509* CreateAndSignX509Certificate() {
  bssl::UniquePtr<X509> x509(X509_new());
  if (!x509) return nullptr;

  // Set validity period for 30 days
  if (!X509_gmtime_adj(X509_getm_notBefore(x509.get()), 0) ||
      !X509_gmtime_adj(X509_getm_notAfter(x509.get()), 60 * 60 * 24 * 30L)) {
    return nullptr;
  }

  bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
  if (!pkey) return nullptr;

  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  if (!bn || !BN_set_word(bn.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr) ||
      !EVP_PKEY_assign_RSA(pkey.get(), rsa.release())) {
    return nullptr;
  }
  if (!X509_set_pubkey(x509.get(), pkey.get())) return nullptr;
  if (X509_sign(x509.get(), pkey.get(), EVP_sha256()) <= 0) return nullptr;

  return x509.release();
}

void RemoveFile(const char* path) {
  if (remove(path) != 0) {
    fprintf(stderr, "Error deleting %s: %s\n", path, strerror(errno));
  }
}

class X509Test : public ::testing::Test {
protected:
  void SetUp() override {
    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);
    ASSERT_GT(createTempFILEpath(signkey_path), 0u);

    bssl::UniquePtr<EVP_PKEY> pkey(EVP_PKEY_new());
    ASSERT_TRUE(pkey);
    bssl::UniquePtr<RSA> rsa(RSA_new());
    ASSERT_TRUE(rsa);
    bssl::UniquePtr<BIGNUM> bn(BN_new());
    ASSERT_TRUE(bn && BN_set_word(bn.get(), RSA_F4) && RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr));
    ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey.get(), rsa.release()));

    ScopedFILE signkey_file(fopen(signkey_path, "wb"));
    ASSERT_TRUE(signkey_file);
    ASSERT_TRUE(PEM_write_PrivateKey(signkey_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));

    x509.reset(CreateAndSignX509Certificate());
    ASSERT_TRUE(x509);

    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));
  }

  void TearDown() override {
    RemoveFile(in_path);
    RemoveFile(out_path);
    RemoveFile(signkey_path);
  }

  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char signkey_path[PATH_MAX];
  bssl::UniquePtr<X509> x509;
};

// Test x509 -in and -out
TEST_F(X509Test, X509ToolTest) {
  args_list_t args = {"-in", in_path, "-out", out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  ScopedFILE out_file(fopen(out_path, "rb"));
  ASSERT_TRUE(out_file);

  bssl::UniquePtr<X509> parsed_x509(PEM_read_X509(out_file.get(), nullptr, nullptr, nullptr));
  ASSERT_TRUE(parsed_x509);
}

// Test -modulus
TEST_F(X509Test, X509ToolModulusTest) {
  args_list_t args = {"-in", in_path, "-modulus"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -signkey
TEST_F(X509Test, X509ToolSignKeyTest) {
  args_list_t args = {"-in", in_path, "-out", out_path, "-signkey", signkey_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -days
TEST_F(X509Test, X509ToolDaysTest) {
  args_list_t args = {"-in", in_path, "-out", out_path, "-signkey", signkey_path, "-days", "365"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -dates
TEST_F(X509Test, X509ToolDatesTest) {
  args_list_t args = {"-in", in_path, "-dates"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -req
TEST_F(X509Test, X509ToolReqTest) {
  bssl::UniquePtr<X509_REQ> req(X509_REQ_new());
  ASSERT_TRUE(req);

  EVP_PKEY* pkey = X509_get_pubkey(x509.get());
  ASSERT_TRUE(pkey);
  X509_REQ_set_pubkey(req.get(), pkey);
  EVP_PKEY_free(pkey);

  ASSERT_TRUE(X509_REQ_sign(req.get(), X509_get0_pubkey(x509.get()), EVP_sha256()));

  ScopedFILE in_file(fopen(in_path, "wb"));
  ASSERT_TRUE(in_file);
  ASSERT_TRUE(PEM_write_X509_REQ(in_file.get(), req.get()));

  args_list_t args = {"-in", in_path, "-out", out_path, "-req", "-signkey", signkey_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test -checkend
TEST_F(X509Test, X509ToolCheckEndTest) {
  args_list_t args = {"-in", in_path, "-checkend", "3600"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);
}

// Test mutually exclusive options, required options, and required arguments
struct MutuallyExclusiveOptionTestParams {
  std::vector<std::string> args;
  const char* description;
};

class X509MutuallyExclusiveOptionsTest : public X509Test, public ::testing::WithParamInterface<MutuallyExclusiveOptionTestParams> {};

INSTANTIATE_TEST_SUITE_P(MutuallyExclusiveOptionsTests, X509MutuallyExclusiveOptionsTest,
                         ::testing::Values(
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-noout", "-out", "out_path"}, "-noout with -out"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-noout", "-modulus"}, "-noout with -modulus"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-noout", "-dates"}, "-noout with -dates"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-noout", "-checkend", "3600"}, "-noout with -checkend"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-req", "-dates"}, "-req with -dates"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-req", "-checkend", "3600"}, "-req with -checkend"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-signkey", "signkey_path", "-dates"}, "-signkey with -dates"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-signkey", "signkey_path", "-checkend", "3600"}, "-signkey with -checkend"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-days", "365", "-dates"}, "-days with -dates"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-days", "365", "-checkend", "3600"}, "-days with -checkend"},
                             MutuallyExclusiveOptionTestParams{{"-out", "output.pem"}, "missing -in"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-req"}, "-req without -signkey"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-checkend", "abc"}, "invalid -checkend (non-numeric)"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-checkend", "-1"}, "invalid -checkend (negative)"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-signkey", "signkey_path", "-days", "abc"}, "invalid -days (non-numeric)"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-signkey", "signkey_path", "-days", "0"}, "invalid -days (zero)"},
                             MutuallyExclusiveOptionTestParams{{"-in", "in_path", "-signkey", "signkey_path", "-days", "-1.7"}, "invalid -days (negative)"}
                         ),
                         [](const ::testing::TestParamInfo<MutuallyExclusiveOptionTestParams>& paramInfo) {
                           return std::string(paramInfo.param.description);
                         });

TEST_P(X509MutuallyExclusiveOptionsTest, MutuallyExclusiveOptions) {
  bool result = X509Tool(GetParam().args);
  ASSERT_FALSE(result);
}
