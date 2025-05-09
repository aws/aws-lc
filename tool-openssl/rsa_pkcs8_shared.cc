// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "rsa_pkcs8_shared.h"
#include <openssl/pem.h>
#include "../tool/internal.h"  // For ScopedFILE definition

namespace awslc_test {

// Creates an EVP_PKEY containing a newly generated RSA key of specified size
EVP_PKEY* CreateTestKey(int key_bits) {
    bssl::UniquePtr<BIGNUM> bn(BN_new());
    if (!bn || !BN_set_word(bn.get(), RSA_F4)) {
        return nullptr;
    }
    
    bssl::UniquePtr<RSA> rsa(RSA_new());
    if (!rsa || !RSA_generate_key_ex(rsa.get(), key_bits, bn.get(), nullptr)) {
        return nullptr;
    }
    
    EVP_PKEY *pkey = EVP_PKEY_new();
    if (!pkey || !EVP_PKEY_assign_RSA(pkey, rsa.release())) {
        EVP_PKEY_free(pkey);
        return nullptr;
    }
    
    return pkey;
}

// Creates a new RSA key with proper ownership semantics via UniquePtr
bssl::UniquePtr<RSA> CreateRSAKey(int key_bits) {
    bssl::UniquePtr<BIGNUM> bn(BN_new());
    if (!bn || !BN_set_word(bn.get(), RSA_F4)) {
        return nullptr;
    }
    
    bssl::UniquePtr<RSA> rsa(RSA_new());
    if (!rsa || !RSA_generate_key_ex(rsa.get(), key_bits, bn.get(), nullptr)) {
        return nullptr;
    }
    
    return rsa;
}

// Validates if a string contains the specified PEM boundary markers
bool CheckKeyBoundaries(const std::string &content, 
                       const std::string &begin1, const std::string &end1, 
                       const std::string &begin2, const std::string &end2) {
    if (content.empty() || begin1.empty() || end1.empty()) {
        return false;
    }
    
    if (content.size() < begin1.size() + end1.size()) {
        return false;
    }
    
    bool primary_match = 
        content.compare(0, begin1.size(), begin1) == 0 && 
        content.compare(content.size() - end1.size(), end1.size(), end1) == 0;
        
    if (primary_match || begin2.empty() || end2.empty()) {
        return primary_match;
    }
    
    if (content.size() < begin2.size() + end2.size()) {
        return false;
    }
    
    return content.compare(0, begin2.size(), begin2) == 0 && 
           content.compare(content.size() - end2.size(), end2.size(), end2) == 0;
}

// Loads and decrypts a private key from a file with optional password
bssl::UniquePtr<EVP_PKEY> DecryptPrivateKey(const char* path, const char* password) {
    if (!path) {
        return nullptr;
    }
    
    ScopedFILE file(fopen(path, "r"));
    if (!file) {
        return nullptr;
    }
    
    return bssl::UniquePtr<EVP_PKEY>(
        PEM_read_PrivateKey(file.get(), nullptr, nullptr, const_cast<char*>(password)));
}

// Compares two EVP_PKEY structures including their private components
bool CompareKeys(EVP_PKEY* key1, EVP_PKEY* key2) {
    if (!key1 || !key2) return false;
    if (EVP_PKEY_id(key1) != EVP_PKEY_id(key2)) return false;
    
    if (EVP_PKEY_id(key1) == EVP_PKEY_RSA) {
        RSA *rsa1 = EVP_PKEY_get0_RSA(key1);
        RSA *rsa2 = EVP_PKEY_get0_RSA(key2);
        
        if (!rsa1 || !rsa2) return false;
        
        const BIGNUM *n1, *e1, *d1, *n2, *e2, *d2;
        RSA_get0_key(rsa1, &n1, &e1, &d1);
        RSA_get0_key(rsa2, &n2, &e2, &d2);
        
        return (BN_cmp(n1, n2) == 0) && 
               (BN_cmp(e1, e2) == 0) && 
               (BN_cmp(d1, d2) == 0);
    }
    
    return false;
}

namespace pem_markers {
    const std::string RSA_BEGIN = "-----BEGIN RSA PRIVATE KEY-----";
    const std::string RSA_END = "-----END RSA PRIVATE KEY-----";
    const std::string PRIVATE_KEY_BEGIN = "-----BEGIN PRIVATE KEY-----";
    const std::string PRIVATE_KEY_END = "-----END PRIVATE KEY-----";
    const std::string ENCRYPTED_PRIVATE_KEY_BEGIN = "-----BEGIN ENCRYPTED PRIVATE KEY-----";
    const std::string ENCRYPTED_PRIVATE_KEY_END = "-----END ENCRYPTED PRIVATE KEY-----";
}

} // namespace awslc_test
