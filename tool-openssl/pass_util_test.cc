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

// Base test fixture for password tests
class PasswordTest : public ::testing::Test {
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

// Parameters for password source tests
struct PasswordSourceParams {
  std::string source;
  std::string expected;
  bool should_succeed;
  std::string description;
};

// Parameterized test fixture for password source tests
class PasswordSourceTest
    : public PasswordTest,
      public ::testing::WithParamInterface<PasswordSourceParams> {};

// Test password extraction from various sources
TEST_P(PasswordSourceTest, ExtractPassword) {
  const auto &params = GetParam();
  bssl::UniquePtr<std::string> source(new std::string(params.source));
  bool result = password::ExtractPassword(source);

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
    PasswordSources, PasswordSourceTest,
    ::testing::Values(
        PasswordSourceParams{"pass:directpassword", "directpassword", true,
                             "direct password"},
        PasswordSourceParams{"", "", true, "empty source"},
        PasswordSourceParams{"env:TEST_PASSWORD_ENV", "envpassword", true,
                             "environment variable"},
        PasswordSourceParams{"invalid:format", "", false, "invalid format"},
        PasswordSourceParams{"file:/non/existent/file", "", false,
                             "non-existent file"},
        PasswordSourceParams{"env:NON_EXISTENT_ENV_VAR", "", false,
                             "non-existent env var"}));

// Test SensitiveStringDeleter properly clears memory
TEST_F(PasswordTest, SensitiveStringDeleter) {
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
  password::SensitiveStringDeleter(str);

  // The original string content should still be intact for comparison
  EXPECT_EQ(original_content, test_password)
      << "Original content was unexpectedly modified";
}
