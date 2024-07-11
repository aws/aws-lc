// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/x509.h"
#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "internal.h"
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
  if (!pkey) {
    return nullptr;
  }
  bssl::UniquePtr<RSA> rsa(RSA_new());
  bssl::UniquePtr<BIGNUM> bn(BN_new());
  if (!bn || !BN_set_word(bn.get(), RSA_F4) ||
      !RSA_generate_key_ex(rsa.get(), 2048, bn.get(), nullptr) ||
      !EVP_PKEY_assign_RSA(pkey.get(), rsa.release())) {
    return nullptr;
  }
  if (!X509_set_pubkey(x509.get(), pkey.get())) {
    return nullptr;
  }

  if (X509_sign(x509.get(), pkey.get(), EVP_sha256()) <= 0) {
    return nullptr;
  }

  return x509.release();
}

void RemoveFile(const char* path) {
  if (remove(path) != 0) {
    fprintf(stderr, "Error deleting %s: %s\n", path, strerror(errno));
  }
}

// Test x509 -in and -out
TEST(X509Test, X509ToolTest) {
  char in_path[PATH_MAX];
  char out_path[PATH_MAX];

  ASSERT_GT(createTempFILEpath(in_path), 0u);
  ASSERT_GT(createTempFILEpath(out_path), 0u);

  bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
  ASSERT_TRUE(x509);

  {
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));
  }

  args_list_t args = {"-in", in_path, "-out", out_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  {
    ScopedFILE out_file(fopen(out_path, "rb"));
    ASSERT_TRUE(out_file);

    bssl::UniquePtr<X509> parsed_x509(PEM_read_X509(out_file.get(), nullptr, nullptr, nullptr));
    ASSERT_TRUE(parsed_x509);
  }

  RemoveFile(in_path);
  RemoveFile(out_path);
}

// Test -modulus
TEST(X509Test, X509ToolModulusTest) {
  char in_path[PATH_MAX];

  ASSERT_GT(createTempFILEpath(in_path), 0u);

  bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
  ASSERT_TRUE(x509);

  {
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));
  }

  args_list_t args = {"-in", in_path, "-modulus"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  RemoveFile(in_path);
}

// Test -signkey
TEST(X509Test, X509ToolSignKeyTest) {
  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char signkey_path[PATH_MAX];

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

  {
    ScopedFILE signkey_file(fopen(signkey_path, "wb"));
    ASSERT_TRUE(signkey_file);
    ASSERT_TRUE(PEM_write_PrivateKey(signkey_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));
  }

  bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
  ASSERT_TRUE(x509);

  {
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));
  }

  args_list_t args = {"-in", in_path, "-out", out_path, "-signkey", signkey_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  RemoveFile(in_path);
  RemoveFile(out_path);
  RemoveFile(signkey_path);
}

// Test -days
TEST(X509Test, X509ToolDaysTest) {
  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char signkey_path[PATH_MAX];

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

  {
    ScopedFILE signkey_file(fopen(signkey_path, "wb"));
    ASSERT_TRUE(signkey_file);
    ASSERT_TRUE(PEM_write_PrivateKey(signkey_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));
  }

  bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
  ASSERT_TRUE(x509);

  {
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));
  }

  args_list_t args = {"-in", in_path, "-out", out_path, "-signkey", signkey_path, "-days", "365"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  RemoveFile(in_path);
  RemoveFile(out_path);
  RemoveFile(signkey_path);
}

// Test -dates
TEST(X509Test, X509ToolDatesTest) {
  char in_path[PATH_MAX];

  ASSERT_GT(createTempFILEpath(in_path), 0u);

  bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
  ASSERT_TRUE(x509);

  {
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));
  }

  args_list_t args = {"-in", in_path, "-dates"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  RemoveFile(in_path);
}

// Test -req
TEST(X509Test, X509ToolReqTest) {
  char in_path[PATH_MAX];
  char out_path[PATH_MAX];
  char signkey_path[PATH_MAX];

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

  {
    ScopedFILE signkey_file(fopen(signkey_path, "wb"));
    ASSERT_TRUE(signkey_file);
    ASSERT_TRUE(PEM_write_PrivateKey(signkey_file.get(), pkey.get(), nullptr, nullptr, 0, nullptr, nullptr));
  }

  bssl::UniquePtr<X509_REQ> req(X509_REQ_new());
  ASSERT_TRUE(req);
  X509_REQ_set_pubkey(req.get(), pkey.get());
  X509_REQ_sign(req.get(), pkey.get(), EVP_sha256());

  {
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509_REQ(in_file.get(), req.get()));
  }

  args_list_t args = {"-in", in_path, "-out", out_path, "-req", "-signkey", signkey_path};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  RemoveFile(in_path);
  RemoveFile(out_path);
  RemoveFile(signkey_path);
}

// Test -checkend
TEST(X509Test, X509ToolCheckEndTest) {
  char in_path[PATH_MAX];

  ASSERT_GT(createTempFILEpath(in_path), 0u);

  bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
  ASSERT_TRUE(x509);

  {
    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    ASSERT_TRUE(PEM_write_X509(in_file.get(), x509.get()));
  }

  args_list_t args = {"-in", in_path, "-checkend", "3600"};
  bool result = X509Tool(args);
  ASSERT_TRUE(result);

  RemoveFile(in_path);
}

// TODO Test mutually exclusive
//(noout && (-out || -modulus || -dates || -checkend))
// (-req && (-dates || -checkend))
// -signkey && (-dates || -checkend))
// -days && (-dates || -checkend))

// TODO Test required options, (-in / -req & -signkey)

// TODO Test against OpenSSL output
// Pass in string argument to executable, copy outputs, check outputs equal
