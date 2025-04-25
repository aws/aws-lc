// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef TEST_UTIL_H
#define TEST_UTIL_H

#include <gtest/gtest.h>
#include <string>
#include <vector>
#include <fstream>
#include <iterator>
#include <string>
#include <iostream>
#include <cctype>
#include <sys/stat.h>
#include <cstring>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/evp.h>
#include "../tool/internal.h"  // For ScopedFILE definition
#include "../crypto/test/test_util.h"


// Helper function to trim whitespace from both ends of a string to test comparison output
static inline std::string &trim(std::string &s) {
  s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](unsigned char ch) {
      return !std::isspace(static_cast<unsigned char>(ch));
  }));
  s.erase(std::find_if(s.rbegin(), s.rend(), [](unsigned char ch) {
      return !std::isspace(static_cast<unsigned char>(ch));
  }).base(), s.end());
  return s;
}


// Helper function to read file content into a string
inline std::string ReadFileToString(const std::string& file_path) {
  std::ifstream file_stream(file_path, std::ios::binary);
  if (!file_stream) {
    return "";
  }
  std::ostringstream buffer;
  buffer << file_stream.rdbuf();
  return buffer.str();
}

inline void RunCommandsAndCompareOutput(const std::string &tool_command, const std::string &openssl_command,
                                        const std::string &out_path_tool, const std::string &out_path_openssl,
                                        std::string &tool_output_str, std::string &openssl_output_str) {
  int tool_result = system(tool_command.c_str());
  ASSERT_EQ(tool_result, 0) << "AWS-LC tool command failed: " << tool_command;

  int openssl_result = system(openssl_command.c_str());
  ASSERT_EQ(openssl_result, 0) << "OpenSSL command failed: " << openssl_command;

  std::ifstream tool_output(out_path_tool);
  tool_output_str = std::string((std::istreambuf_iterator<char>(tool_output)), std::istreambuf_iterator<char>());
  std::ifstream openssl_output(out_path_openssl);
  openssl_output_str = std::string((std::istreambuf_iterator<char>(openssl_output)), std::istreambuf_iterator<char>());

  std::cout << "AWS-LC tool output:" << std::endl << tool_output_str << std::endl;
  std::cout << "OpenSSL output:" << std::endl << openssl_output_str << std::endl;
}

inline void RemoveFile(const char* path) {
  struct stat buffer;
  if (path != nullptr && stat(path, &buffer) == 0) {
    if (remove(path) != 0) {
      fprintf(stderr, "Error deleting %s: %s\n", path, strerror(errno));
    }
  }
}

// OpenSSL versions 3.1.0 and later change from "(stdin)= " to "MD5(stdin) ="
std::string GetHash(const std::string& str);

// Helper function to decrypt a PEM private key file using the provided password
inline bssl::UniquePtr<EVP_PKEY> DecryptPrivateKey(const char* path, const char* password) {
  ScopedFILE file(fopen(path, "r"));
  if (!file) return nullptr;
  
  return bssl::UniquePtr<EVP_PKEY>(
      PEM_read_PrivateKey(file.get(), nullptr, nullptr, const_cast<char*>(password)));
}

// Helper method to compare two EVP_PKEY structures for equality
inline bool CompareKeys(EVP_PKEY* key1, EVP_PKEY* key2) {
  if (!key1 || !key2) return false;
  if (EVP_PKEY_id(key1) != EVP_PKEY_id(key2)) return false;
  
  if (EVP_PKEY_id(key1) == EVP_PKEY_RSA) {
    RSA *rsa1 = EVP_PKEY_get0_RSA(key1);
    RSA *rsa2 = EVP_PKEY_get0_RSA(key2);
    
    // Compare modulus, public exponent, and private exponent
    const BIGNUM *n1, *e1, *d1, *n2, *e2, *d2;
    RSA_get0_key(rsa1, &n1, &e1, &d1);
    RSA_get0_key(rsa2, &n2, &e2, &d2);
    
    return (BN_cmp(n1, n2) == 0) && 
           (BN_cmp(e1, e2) == 0) && 
           (BN_cmp(d1, d2) == 0);
  }
  
  // If not RSA, you could add more key type comparisons here
  return false;
}

#endif //TEST_UTIL_H
