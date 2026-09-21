// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef TEST_UTIL_H
#define TEST_UTIL_H

#include <gtest/gtest.h>
#include <openssl/base.h>
#include <sys/stat.h>
#if !defined(OPENSSL_WINDOWS)
#include <sys/wait.h>
#endif
#include <cctype>
#include <cstring>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <vector>
#include "../crypto/test/test_util.h"

// Helper function to trim whitespace from both ends of a string to test
// comparison output
static inline std::string &trim(std::string &s) {
  s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](unsigned char ch) {
            return !std::isspace(static_cast<unsigned char>(ch));
          }));
  s.erase(std::find_if(s.rbegin(), s.rend(),

                       [](unsigned char ch) {
                         return !std::isspace(static_cast<unsigned char>(ch));
                       })

              .base(),

          s.end());
  return s;
}

// Helper function to read file content into a string
inline std::string ReadFileToString(const std::string &file_path) {
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

inline int ExecuteCommand(const std::string &command) {
#if defined(OPENSSL_WINDOWS)
  // cmd.exe strips the first and last quotes from a command beginning with a
  // quoted executable. Add outer quotes to preserve the executable and args.
  if (!command.empty() && command.front() == '"') {
    return system(("\"" + command + "\"").c_str());
  }
#endif
  return system(command.c_str());
}

inline void RunCommandsAndCompareOutput(const std::string &tool_command,
                                        const std::string &openssl_command,
                                        const std::string &out_path_tool,
                                        const std::string &out_path_openssl,
                                        std::string &tool_output_str,
                                        std::string &openssl_output_str) {
  int tool_result = ExecuteCommand(tool_command);
  ASSERT_EQ(tool_result, 0) << "AWS-LC tool command failed: " << tool_command;

  int openssl_result = ExecuteCommand(openssl_command);
  ASSERT_EQ(openssl_result, 0) << "OpenSSL command failed: " << openssl_command;

  std::ifstream tool_output(out_path_tool);
  tool_output_str = std::string((std::istreambuf_iterator<char>(tool_output)),
                                std::istreambuf_iterator<char>());
  std::ifstream openssl_output(out_path_openssl);
  openssl_output_str =
      std::string((std::istreambuf_iterator<char>(openssl_output)),
                  std::istreambuf_iterator<char>());

  std::cout << "AWS-LC tool output:" << std::endl
            << tool_output_str << std::endl;
  std::cout << "OpenSSL output:" << std::endl
            << openssl_output_str << std::endl;
}

inline void RemoveFile(const char *path) {
  struct stat buffer;
  if (path != nullptr && stat(path, &buffer) == 0) {
    if (remove(path) != 0) {
      fprintf(stderr, "Error deleting %s: %s\n", path, strerror(errno));
    }
  }
}


// ExecuteCommandExitCode runs |command| and returns the process exit code, or
// -1 if the command could not be run or did not exit normally.
inline int ExecuteCommandExitCode(const std::string &command) {
  int status = ExecuteCommand(command);
#if defined(OPENSSL_WINDOWS)
  return status;
#else
  if (status == -1 || !WIFEXITED(status)) {
    return -1;
  }
  return WEXITSTATUS(status);
#endif
}

// OpenSSL versions 3.1.0 and later change from "(stdin)= " to "MD5(stdin)
// ="
std::string GetHash(const std::string &str);
void CreateAndSignX509Certificate(bssl::UniquePtr<X509> &x509,
                                  bssl::UniquePtr<EVP_PKEY> *pkey);
bssl::UniquePtr<X509_REQ> LoadPEMCSR(const char *path);
bssl::UniquePtr<X509_REQ> LoadDERCSR(const char *path);
bssl::UniquePtr<X509> LoadPEMCertificate(const char *path);
bssl::UniquePtr<X509> LoadDERCertificate(const char *path);
bool CompareCSRs(X509_REQ *csr1, X509_REQ *csr2);
bool CheckCertificateValidityPeriod(X509 *cert, int expected_days);
bool CompareCertificates(X509 *cert1, X509 *cert2, X509 *ca_cert,
                         int expected_days);
EVP_PKEY *DecryptPrivateKey(const char *path, const char *password);
bool CompareKeyEquality(EVP_PKEY *key1, EVP_PKEY *key2);
bool CompareRandomGeneratedKeys(EVP_PKEY *key1, EVP_PKEY *key2,
                                unsigned int expected_bits);
bool ValidateCertificateKeyPair(X509 *cert, EVP_PKEY *private_key);


// Additional PEM format boundary markers used by PKCS8
const std::string PRIVATE_KEY_BEGIN = "-----BEGIN PRIVATE KEY-----";
const std::string PRIVATE_KEY_END = "-----END PRIVATE KEY-----";
const std::string ENCRYPTED_PRIVATE_KEY_BEGIN =
    "-----BEGIN ENCRYPTED PRIVATE KEY-----";
const std::string ENCRYPTED_PRIVATE_KEY_END =
    "-----END ENCRYPTED PRIVATE KEY-----";

// CheckKeyBoundaries checks the PEM boundary markers of |content|
bool CheckKeyBoundaries(const std::string &content,
                        const std::string &begin1,
                        const std::string &end1,
                        const std::string &begin2,
                        const std::string &end2);

#endif  // TEST_UTIL_H
