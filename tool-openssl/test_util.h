// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef TEST_UTIL_H
#define TEST_UTIL_H

#include <gtest/gtest.h>
#include <sys/stat.h>
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
