// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "openssl/x509.h"
#include <openssl/err.h>
#include <gtest/gtest.h>
#include <stdio.h>
#include <string>
#include <vector>
#include <memory>
#include "../tool/internal.h"
#include "internal.h"

X509* CreateAndSignX509Certificate() {
  X509 *x509 = X509_new();
  if (!x509) return nullptr;

  // Set validity period
  if (!X509_gmtime_adj(X509_getm_notBefore(x509), 0) ||
      !X509_gmtime_adj(X509_getm_notAfter(x509), 31536000L)) {
    X509_free(x509);
    return nullptr;
      }

  // Generate and set the public key
  EVP_PKEY *pkey = EVP_PKEY_new();
  if (!pkey) {
    X509_free(x509);
    return nullptr;
  }
  RSA *rsa = RSA_new();
  BIGNUM *bn = BN_new();
  if (!bn || !BN_set_word(bn, RSA_F4) ||
      !RSA_generate_key_ex(rsa, 2048, bn, nullptr) ||
      !EVP_PKEY_assign_RSA(pkey, rsa)) {
    BN_free(bn);
    EVP_PKEY_free(pkey);
    X509_free(x509);
    return nullptr;
      }
  BN_free(bn);
  if (!X509_set_pubkey(x509, pkey)) {
    EVP_PKEY_free(pkey);
    X509_free(x509);
    return nullptr;
  }

  // Sign certificate
  if (X509_sign(x509, pkey, EVP_sha256()) <= 0) {
    EVP_PKEY_free(pkey);
    X509_free(x509);
    return nullptr;
  }

  EVP_PKEY_free(pkey);
  return x509;
}

// Test x509 -in and -out
TEST(X509Test, X509ToolTest) {
    std::string in_path = "test_input.der";
    std::string out_path = "test_output.der";

    std::unique_ptr<X509, decltype(&X509_free)> x509(CreateAndSignX509Certificate(), X509_free);
    ASSERT_TRUE(x509 != nullptr);

    // Serialize certificate to DER format
    uint8_t *der_data = nullptr;
    int len = i2d_X509(x509.get(), &der_data);
    if (len <= 0) {
        ERR_print_errors_fp(stderr);
    }
    ASSERT_GT(len, 0);

    FILE *in_file = fopen(in_path.c_str(), "wb");
    ASSERT_TRUE(in_file != nullptr);
    fwrite(der_data, 1, len, in_file);
    fclose(in_file);
    OPENSSL_free(der_data);

    // Set up x509 tool arguments
    args_list_t args = {"-in", in_path, "-out", out_path};

    // Call x509 tool function
    bool result = X509Tool(args);
    ASSERT_TRUE(result);

    // Read and verify output file
    FILE *out_file = fopen(out_path.c_str(), "rb");
    ASSERT_TRUE(out_file != nullptr);

    std::vector<uint8_t> output_data;
    ASSERT_TRUE(ReadAll(&output_data, out_file));
    fclose(out_file);

    // Ensure output data not empty
    ASSERT_FALSE(output_data.empty());

    // Parse x509 cert from output file
    const uint8_t *p = output_data.data();
    std::unique_ptr<X509, decltype(&X509_free)> parsed_x509(d2i_X509(nullptr, &p, output_data.size()), X509_free);
    ASSERT_TRUE(parsed_x509 != nullptr);

    remove(in_path.c_str());
    remove(out_path.c_str());
}

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
