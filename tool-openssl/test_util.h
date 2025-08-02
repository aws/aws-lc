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
  fprintf(stderr, "DEBUG: ReadFileToString - Starting for path: %s\n", file_path.c_str());
  
  if (file_path.empty()) {
    fprintf(stderr, "DEBUG: ReadFileToString - Empty file path provided\n");
    return "";
  }
  
  // Check if file exists first
  fprintf(stderr, "DEBUG: ReadFileToString - Checking if file exists with stat()\n");
  struct stat stat_buffer;
  int stat_result = stat(file_path.c_str(), &stat_buffer);
  if (stat_result != 0) {
    fprintf(stderr, "DEBUG: ReadFileToString - stat() failed with error code: %d, errno: %d\n", 
            stat_result, errno);
    return "";
  }
  fprintf(stderr, "DEBUG: ReadFileToString - File exists, size: %lld bytes\n", 
          (long long)stat_buffer.st_size);

  fprintf(stderr, "DEBUG: ReadFileToString - Opening file stream\n");
  std::ifstream file_stream(file_path, std::ios::binary);
  if (!file_stream.is_open()) {
    fprintf(stderr, "DEBUG: ReadFileToString - Failed to open file stream, errno: %d\n", errno);
    return "";
  }
  fprintf(stderr, "DEBUG: ReadFileToString - File stream opened successfully\n");
  
  fprintf(stderr, "DEBUG: ReadFileToString - Creating output buffer and reading file content\n");
  std::ostringstream output_buffer;
  
  // Check stream state before reading
  if (file_stream.good()) {
    output_buffer << file_stream.rdbuf();
    fprintf(stderr, "DEBUG: ReadFileToString - File content read into buffer\n");
  } else {
    fprintf(stderr, "DEBUG: ReadFileToString - File stream not in good state before reading\n");
    return "";
  }
  
  // Check stream state after reading
  if (!file_stream.good() && !file_stream.eof()) {
    fprintf(stderr, "DEBUG: ReadFileToString - File stream in bad state after reading, error flags: %d\n", 
            (int)file_stream.rdstate());
    return "";
  }
  
  std::string result = output_buffer.str();
  fprintf(stderr, "DEBUG: ReadFileToString - Created result string, length: %zu bytes\n", result.length());
  
  fprintf(stderr, "DEBUG: ReadFileToString - Closing file stream\n");
  file_stream.close();
  if (file_stream.fail()) {
    fprintf(stderr, "DEBUG: ReadFileToString - Warning: Error closing file stream\n");
  }
  
  fprintf(stderr, "DEBUG: ReadFileToString - Returning result\n");
  return result;
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
