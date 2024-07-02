// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/x509.h"
#include <openssl/err.h>
#include <gtest/gtest.h>
#include "../tool/internal.h"
#include "internal.h"

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

X509* CreateAndSignX509Certificate() {
  bssl::UniquePtr<X509> x509(X509_new());
  if (!x509) return nullptr;

  // Set validity period for 1 year
  if (!X509_gmtime_adj(X509_getm_notBefore(x509.get()), 0) ||
      !X509_gmtime_adj(X509_getm_notAfter(x509.get()), 31536000L)) {
    return nullptr;
  }

  // Generate and set the public key
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

  // Sign certificate
  if (X509_sign(x509.get(), pkey.get(), EVP_sha256()) <= 0) {
    return nullptr;
  }

  return x509.release();
}

// Test x509 -in and -out
TEST(X509Test, X509ToolTest) {
    char in_path[PATH_MAX];
    char out_path[PATH_MAX];

    ASSERT_GT(createTempFILEpath(in_path), 0u);
    ASSERT_GT(createTempFILEpath(out_path), 0u);

    bssl::UniquePtr<X509> x509(CreateAndSignX509Certificate());
    ASSERT_TRUE(x509);

    // Serialize certificate to DER format
    uint8_t *der_data = nullptr;
    int len = i2d_X509(x509.get(), &der_data);
    ASSERT_GT(static_cast<size_t>(len), 0u);

    ScopedFILE in_file(fopen(in_path, "wb"));
    ASSERT_TRUE(in_file);
    fwrite(der_data, 1, len, in_file.get());
    OPENSSL_free(der_data);

    in_file.reset();

    // Set up x509 tool arguments
    args_list_t args = {"-in", in_path, "-out", out_path};

    // Call x509 tool function
    bool result = X509Tool(args);
    ASSERT_TRUE(result);

    // Read and verify output file
    ScopedFILE out_file(fopen(out_path, "rb"));
    ASSERT_TRUE(out_file);

    std::vector<uint8_t> output_data;
    ASSERT_TRUE(ReadAll(&output_data, out_file.get()));

    // Ensure output data not empty
    ASSERT_FALSE(output_data.empty());

    // Parse x509 cert from output file
    const uint8_t *p = output_data.data();
    bssl::UniquePtr<X509> parsed_x509(d2i_X509(nullptr, &p, output_data.size()));
    ASSERT_TRUE(parsed_x509);

    remove(in_path);
    remove(out_path);
}
