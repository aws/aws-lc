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

// External constants from rsa_test.cc
extern const std::string RSA_BEGIN;
extern const std::string RSA_END;
extern const std::string BEGIN;
extern const std::string END;
extern const std::string MODULUS;

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
  if (file_path.empty()) {
    return "";
  }
  
  // Check if file exists first
  struct stat stat_buffer;
  if (stat(file_path.c_str(), &stat_buffer) != 0) {
    return "";
  }

  std::ifstream file_stream(file_path, std::ios::binary);
  if (!file_stream.is_open()) {
    return "";
  }
  
  std::ostringstream output_buffer;
  output_buffer << file_stream.rdbuf();
  
  return output_buffer.str();
}

// Function declarations (implementations in pkcs8_test.cc)
EVP_PKEY* CreateTestKey(int key_bits = 2048);
bool CheckKeyBoundaries(const std::string &content, 
                       const std::string &begin1, const std::string &end1, 
                       const std::string &begin2 = "", const std::string &end2 = "");
bssl::UniquePtr<EVP_PKEY> DecryptPrivateKey(const char* path, const char* password);
bool CompareKeys(EVP_PKEY* key1, EVP_PKEY* key2);

// Implementation of the TestKeyToolOptionErrors template function
// Tests for expected error conditions when invalid options are provided to CLI tools
template<typename ToolFunc>
void TestKeyToolOptionErrors(ToolFunc tool_func, const std::vector<std::string>& args) {
    if (args.empty()) {
        ADD_FAILURE() << "Empty argument list provided to TestKeyToolOptionErrors";
        return;
    }
    
    args_list_t c_args;
    for (const auto& arg : args) {
        c_args.push_back(arg.c_str());
    }
    
    bool result = tool_func(c_args);
    ASSERT_FALSE(result) << "Expected error not triggered for args: " 
                        << args[0] << (args.size() > 1 ? "..." : "");
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

#endif //TEST_UTIL_H
