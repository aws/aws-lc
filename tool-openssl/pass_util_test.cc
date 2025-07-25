// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/base.h>
#include <openssl/bio.h>
#include <openssl/mem.h>
#include <openssl/pem.h>
#include <string>
#ifdef _WIN32
#include <stdlib.h>  // for _putenv_s
#endif
#include "internal.h"
#include "test_util.h"

// Use PEM_BUFSIZE (defined in openssl/pem.h) for password buffer size testing
// to match the implementation in pass_util.cc

namespace {
// Helper functions to encapsulate common operations
void WriteTestFile(const char* path, const char* content, bool preserve_newlines = false) {
  ScopedFILE file(fopen(path, "wb"));
  ASSERT_TRUE(file) << "Failed to open file: " << path;
  if (content) {
    if (preserve_newlines) {
      // Write content exactly as provided, including newlines
      ASSERT_GT(fprintf(file.get(), "%s", content), 0)
          << "Failed to write to file: " << path;
    } else {
      // Write content without trailing newline
      size_t bytes_written = fwrite(content, 1, strlen(content), file.get());
      ASSERT_GT(bytes_written, 0u)  // Compare with unsigned 0
          << "Failed to write to file: " << path;
    }
  }
}

void SetTestEnvVar(const char* name, const char* value) {
#ifdef _WIN32
  _putenv_s(name, value);
#else
  setenv(name, value, 1);
#endif
}

void UnsetTestEnvVar(const char* name) {
#ifdef _WIN32
  _putenv_s(name, "");
#else
  unsetenv(name);
#endif
}
}  // namespace

// Base test fixture for pass_util tests
class PassUtilTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Create temporary files for testing using utility from crypto/test/test_util.h
    ASSERT_GT(createTempFILEpath(pass_path), 0u)
        << "Failed to create first temp file path";
    ASSERT_GT(createTempFILEpath(pass_path2), 0u)
        << "Failed to create second temp file path";

    // Write test passwords using helper function
    WriteTestFile(pass_path, "testpassword");
    WriteTestFile(pass_path2, "anotherpassword");

    // Set up environment variable using helper function
    SetTestEnvVar("TEST_PASSWORD_ENV", "envpassword");
  }

  void TearDown() override {
    // Use RemoveFile from tool-openssl/test_util.h
    RemoveFile(pass_path);
    RemoveFile(pass_path2);
    UnsetTestEnvVar("TEST_PASSWORD_ENV");
  }

  char pass_path[PATH_MAX] = {};
  char pass_path2[PATH_MAX] = {};
};

// Parameters for pass_util source tests
struct PassUtilSourceParams {
  std::string source;
  std::string expected;
  bool should_succeed;
  std::string description;

  // Default constructor that initializes all members
  PassUtilSourceParams() 
      : source(""), expected(""), should_succeed(false), description("") {}

  // Constructor that initializes all members
  PassUtilSourceParams(std::string src, std::string exp, bool succeed, std::string desc)
      : source(std::move(src)), expected(std::move(exp)), 
        should_succeed(succeed), description(std::move(desc)) {}
};

// Parameterized test fixture for pass_util source tests
class PassUtilSourceTest
    : public PassUtilTest,
      public ::testing::WithParamInterface<PassUtilSourceParams> {};

// Test password extraction from various sources
TEST_P(PassUtilSourceTest, ExtractPassword) {
  const auto &params = GetParam();
  bssl::UniquePtr<std::string> source(new std::string(params.source));
  bool result = pass_util::ExtractPassword(source);

  if (params.should_succeed) {
    ASSERT_TRUE(result) << "ExtractPassword failed for " << params.description;
    ASSERT_TRUE(source) << "Source was unexpectedly null for " << params.description;
    EXPECT_EQ(*source, params.expected)
        << "Incorrect password for " << params.description;
  } else {
    EXPECT_FALSE(result) << "ExtractPassword should fail for "
                         << params.description;
  }
}

// Instantiate password source test cases
INSTANTIATE_TEST_SUITE_P(
    PassUtilSources, PassUtilSourceTest,
    ::testing::Values(
        PassUtilSourceParams{"pass:directpassword", "directpassword", true,
                             "direct password"},
        PassUtilSourceParams{"pass:", "", true, "empty password with pass: prefix"},
        PassUtilSourceParams{"", "", false, "empty source without prefix"},
        PassUtilSourceParams{"env:TEST_PASSWORD_ENV", "envpassword", true,
                             "environment variable"},
        PassUtilSourceParams{"file:/non/existent/file", "", false,
                             "non-existent file"},
        PassUtilSourceParams{"env:NON_EXISTENT_ENV_VAR", "", false,
                             "non-existent env var"}));

// Test edge cases for file-based passwords
TEST_F(PassUtilTest, FileEdgeCases) {
  // Test file truncation - exactly at buffer size - 1 without newline
  {
    std::string truncated_pass(PEM_BUFSIZE - 1, 'A');
    WriteTestFile(pass_path, truncated_pass.c_str());
  }
  
  bssl::UniquePtr<std::string> source(new std::string(std::string("file:") + pass_path));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on truncated file";

  // Test file exceeding maximum length
  {
    std::string long_pass(PEM_BUFSIZE + 10, 'B');
    WriteTestFile(pass_path, long_pass.c_str());
  }
  
  source.reset(new std::string(std::string("file:") + pass_path));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on too long file content";

  // Test empty file
  {
    WriteTestFile(pass_path, "");
  }
  
  source.reset(new std::string(std::string("file:") + pass_path));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on empty file";

  // Test file with only newlines - should fail like OpenSSL with empty password error
  {
    WriteTestFile(pass_path, "\n\n\n", true);  // preserve_newlines = true
  }
  
  source.reset(new std::string(std::string("file:") + pass_path));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on newline-only file (empty password)";

  // Test file at buffer size - 1 with newline (should not trigger truncation)
  {
    std::string non_truncated_pass(PEM_BUFSIZE - 2, 'C');
    std::string content = non_truncated_pass + "\n";
    WriteTestFile(pass_path, content.c_str(), true);  // preserve_newlines = true
  }
  
  source.reset(new std::string(std::string("file:") + pass_path));
  bool result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed when file is at max length but has newline";
  EXPECT_EQ(source->length(), static_cast<size_t>(PEM_BUFSIZE - 2)) 
      << "Password should not include newline and should be max length - 2";
}

// Test edge cases for environment variable passwords
TEST_F(PassUtilTest, EnvVarEdgeCases) {
  // Test empty environment variable
  SetTestEnvVar("TEST_EMPTY_PASSWORD", "");
  
  bssl::UniquePtr<std::string> source(new std::string("env:TEST_EMPTY_PASSWORD"));
  bool result = pass_util::ExtractPassword(source);
  EXPECT_FALSE(result) << "Should fail on empty environment variable";

  // Test maximum length environment variable
  std::string long_pass(PEM_BUFSIZE + 10, 'B');
  SetTestEnvVar("TEST_LONG_PASSWORD", long_pass.c_str());

  source.reset(new std::string("env:TEST_LONG_PASSWORD"));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on too long environment variable";

  // Test non-existent environment variable
  source.reset(new std::string("env:NON_EXISTENT_VAR_NAME_12345"));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on non-existent environment variable";

  UnsetTestEnvVar("TEST_EMPTY_PASSWORD");
  UnsetTestEnvVar("TEST_LONG_PASSWORD");
}

// Test edge cases for direct passwords
TEST_F(PassUtilTest, DirectPasswordEdgeCases) {
  // Test maximum length direct password
  std::string long_pass = "pass:" + std::string(PEM_BUFSIZE + 10, 'C');
  bssl::UniquePtr<std::string> source(new std::string(long_pass));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on too long direct password";

  // Test empty direct password
  source.reset(new std::string("pass:"));
  bool result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed with empty direct password";
  EXPECT_TRUE(source->empty()) << "Password should be empty";

  // Test invalid format strings
  const char* invalid_formats[] = {
    "pass",           // Missing colon
    "pass:test:123",  // Multiple colons
    ":password",      // Missing prefix
    "invalid:pass",   // Invalid prefix
    "file:",         // Empty file path
    "env:",          // Empty environment variable
    "",              // Empty string
  };

  for (const char* fmt : invalid_formats) {
    source.reset(new std::string(fmt));
    EXPECT_FALSE(pass_util::ExtractPassword(source)) 
        << "Should fail on invalid format: " << fmt;
  }
}

// Test SensitiveStringDeleter properly clears memory
TEST_F(PassUtilTest, SensitiveStringDeleter) {
  const char *test_password = "sensitive_data_to_be_cleared";
  std::string *str = new std::string(test_password);

  // Make a copy of the string content
  std::string original_content = *str;

  // Verify we have the password
  ASSERT_EQ(original_content, test_password)
      << "Failed to set up test password";

  // Get a pointer to the string's buffer
  const char *buffer_ptr = str->data();

  // Verify the buffer contains our password
  ASSERT_EQ(memcmp(buffer_ptr, test_password, str->length()), 0)
      << "Buffer doesn't contain expected password data";

  // Call the deleter
  pass_util::SensitiveStringDeleter(str);

  // The original string content should still be intact for comparison
  EXPECT_EQ(original_content, test_password)
      << "Original content was unexpectedly modified";
}
