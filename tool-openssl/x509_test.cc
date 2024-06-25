/* Copyright (c) 2014, Google Inc.
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
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include "openssl/x509.h"
#include <openssl/err.h>
#include <gtest/gtest.h>
#include <stdio.h>
#include <string>
#include <vector>
#include "../tool/internal.h"
#include "internal.h"

// Test x509 -in and -out
TEST(X509Test, X509ToolTest) {
    std::string in_path = "test_input.der";
    std::string out_path = "test_output.der";

    X509 *x509 = X509_new();
    ASSERT_TRUE(x509 != nullptr);

    // Set validity period
    ASSERT_TRUE(X509_gmtime_adj(X509_getm_notBefore(x509), 0));
    ASSERT_TRUE(X509_gmtime_adj(X509_getm_notAfter(x509), 31536000L));

    // Generate and set the public key
    EVP_PKEY *pkey = EVP_PKEY_new();
    ASSERT_TRUE(pkey != nullptr);
    RSA *rsa = RSA_new();
    BIGNUM *bn = BN_new();
    ASSERT_TRUE(bn != nullptr);
    ASSERT_TRUE(BN_set_word(bn, RSA_F4));
    ASSERT_TRUE(RSA_generate_key_ex(rsa, 2048, bn, nullptr));
    ASSERT_TRUE(EVP_PKEY_assign_RSA(pkey, rsa));
    BN_free(bn);
    ASSERT_TRUE(X509_set_pubkey(x509, pkey));

    // Sign certificate
    ASSERT_TRUE(X509_sign(x509, pkey, EVP_sha256()) > 0);
    EVP_PKEY_free(pkey);

    // Serialize certificate to DER format
    uint8_t *der_data = nullptr;
    int len = i2d_X509(x509, &der_data);
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
    X509 *parsed_x509 = d2i_X509(nullptr, &p, output_data.size());
    ASSERT_TRUE(parsed_x509 != nullptr);

    X509_free(parsed_x509);
    X509_free(x509);
    remove(in_path.c_str());
    remove(out_path.c_str());
}

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}