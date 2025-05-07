// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef RSA_PKCS8_SHARED_H
#define RSA_PKCS8_SHARED_H

#include <openssl/rsa.h>
#include <openssl/evp.h>
#include <string>
#include <vector>
#include "test_util.h"

namespace awslc_test {

// Creates an EVP_PKEY containing a newly generated RSA key
EVP_PKEY* CreateTestKey(int key_bits = 2048);

// Creates a new RSA key with proper ownership semantics
bssl::UniquePtr<RSA> CreateRSAKey(int key_bits = 2048);

// Validates if content has the specified PEM boundary markers
bool CheckKeyBoundaries(const std::string &content, 
                        const std::string &begin1, const std::string &end1, 
                        const std::string &begin2 = "", const std::string &end2 = "");

// Decrypts a PEM private key file using the provided password
bssl::UniquePtr<EVP_PKEY> DecryptPrivateKey(const char* path, const char* password);

// Compares two EVP_PKEY structures including private components
bool CompareKeys(EVP_PKEY* key1, EVP_PKEY* key2);

// Tests CLI tool error conditions with custom error reporting
template<typename ToolFunc>
void TestKeyToolOptionErrors(ToolFunc tool_func, const std::vector<std::string>& args);

// PEM format boundary markers used by various key formats
namespace pem_markers {
    // RSA-specific format markers
    extern const std::string RSA_BEGIN;
    extern const std::string RSA_END;
    
    // Generic private key format markers (PKCS8 format)
    extern const std::string PRIVATE_KEY_BEGIN;
    extern const std::string PRIVATE_KEY_END;
    
    // Encrypted private key format markers
    extern const std::string ENCRYPTED_PRIVATE_KEY_BEGIN;
    extern const std::string ENCRYPTED_PRIVATE_KEY_END;
}

} // namespace awslc_test

// Template implementation must be visible where used
#include "rsa_pkcs8_shared.inl"

#endif // RSA_PKCS8_SHARED_H
