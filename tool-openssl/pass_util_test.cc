// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/base.h>
#include <openssl/bio.h>
#include <openssl/mem.h>
#include <string>
#ifdef _WIN32
#include <stdlib.h>  // for _putenv_s
#endif
#include "internal.h"
#include "test_util.h"

// Maximum length limit for sensitive strings like passwords (4KB)
static constexpr size_t DEFAULT_MAX_SENSITIVE_STRING_LENGTH = 4096;

// Base test fixture for pass_util tests
class PassUtilTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Create temporary files for testing
    ASSERT_GT(createTempFILEpath(pass_path), 0u)
        << "Failed to create first temp file path";
    ASSERT_GT(createTempFILEpath(pass_path2), 0u)
        << "Failed to create second temp file path";

    // Write test passwords to files using ScopedFILE
    {
      ScopedFILE file1(fopen(pass_path, "wb"));
      ASSERT_TRUE(file1) << "Failed to open first password file";
      ASSERT_GT(fprintf(file1.get(), "testpassword"), 0)
          << "Failed to write first password";
    }

    {
      ScopedFILE file2(fopen(pass_path2, "wb"));
      ASSERT_TRUE(file2) << "Failed to open second password file";
      ASSERT_GT(fprintf(file2.get(), "anotherpassword"), 0)
          << "Failed to write second password";
    }

    // Set up environment variable for testing
#ifdef _WIN32
    // Windows version
    _putenv_s("TEST_PASSWORD_ENV", "envpassword");
#else
    // POSIX version
    setenv("TEST_PASSWORD_ENV", "envpassword", 1);
#endif
  }

  void TearDown() override {
    RemoveFile(pass_path);
    RemoveFile(pass_path2);
#ifdef _WIN32
    // Windows version - setting to empty string removes the variable
    _putenv_s("TEST_PASSWORD_ENV", "");
#else
    // POSIX version
    unsetenv("TEST_PASSWORD_ENV");
#endif
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
  // Test file truncation
  {
    ScopedFILE file(fopen(pass_path, "wb"));
    ASSERT_TRUE(file) << "Failed to open password file";
    // Write a very long string that exceeds DEFAULT_MAX_SENSITIVE_STRING_LENGTH
    std::string long_pass(DEFAULT_MAX_SENSITIVE_STRING_LENGTH + 10, 'A');
    ASSERT_GT(fprintf(file.get(), "%s", long_pass.c_str()), 0);
  }
  
  bssl::UniquePtr<std::string> source(new std::string(std::string("file:") + pass_path));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on too long file content";

  // Test empty file
  {
    ScopedFILE file(fopen(pass_path, "wb"));
    ASSERT_TRUE(file) << "Failed to open password file";
    // Write nothing, creating an empty file
  }
  
  source.reset(new std::string(std::string("file:") + pass_path));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on empty file";

  // Test file with only newlines
  {
    ScopedFILE file(fopen(pass_path, "wb"));
    ASSERT_TRUE(file) << "Failed to open password file";
    ASSERT_GT(fprintf(file.get(), "\n\n\n"), 0);
  }
  
  source.reset(new std::string(std::string("file:") + pass_path));
  bool result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed with empty password from newline-only file";
  EXPECT_TRUE(source->empty()) << "Password should be empty from newline-only file";
}

// Test edge cases for environment variable passwords
TEST_F(PassUtilTest, EnvVarEdgeCases) {
  // Test empty environment variable
#ifdef _WIN32
  _putenv_s("TEST_EMPTY_PASSWORD", "");
#else
  setenv("TEST_EMPTY_PASSWORD", "", 1);
#endif
  
  bssl::UniquePtr<std::string> source(new std::string("env:TEST_EMPTY_PASSWORD"));
  bool result = pass_util::ExtractPassword(source);
  EXPECT_FALSE(result) << "Should fail on empty environment variable";

  // Test maximum length environment variable
  std::string long_pass(DEFAULT_MAX_SENSITIVE_STRING_LENGTH + 10, 'B');
#ifdef _WIN32
  _putenv_s("TEST_LONG_PASSWORD", long_pass.c_str());
#else
  setenv("TEST_LONG_PASSWORD", long_pass.c_str(), 1);
#endif

  source.reset(new std::string("env:TEST_LONG_PASSWORD"));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on too long environment variable";

  // Test non-existent environment variable
  source.reset(new std::string("env:NON_EXISTENT_VAR_NAME_12345"));
  EXPECT_FALSE(pass_util::ExtractPassword(source)) << "Should fail on non-existent environment variable";

#ifdef _WIN32
  _putenv_s("TEST_EMPTY_PASSWORD", "");
  _putenv_s("TEST_LONG_PASSWORD", "");
#else
  unsetenv("TEST_EMPTY_PASSWORD");
  unsetenv("TEST_LONG_PASSWORD");
#endif
}

// Test edge cases for direct passwords
TEST_F(PassUtilTest, DirectPasswordEdgeCases) {
  // Test maximum length direct password
  std::string long_pass = "pass:" + std::string(DEFAULT_MAX_SENSITIVE_STRING_LENGTH + 10, 'C');
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
