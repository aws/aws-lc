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
void WriteTestFile(const char *path, const char *content,
                   bool preserve_newlines = false) {
  ScopedFILE file(fopen(path, "wb"));
  ASSERT_TRUE(file) << "Failed to open file: " << path;
  if (content && strlen(content) > 0) {
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
  // If content is NULL or empty, we just create an empty file (no assertion
  // needed)
}

void SetTestEnvVar(const char *name, const char *value) {
#ifdef _WIN32
  _putenv_s(name, value);
#else
  setenv(name, value, 1);
#endif
}

void UnsetTestEnvVar(const char *name) {
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
    // Create temporary files for testing using utility from
    // crypto/test/test_util.h
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


TEST_F(PassUtilTest, FileEdgeCases) {
  // Test file truncation - exactly at buffer size - 1 without newline
  {
    std::string truncated_pass(PEM_BUFSIZE - 1, 'A');
    WriteTestFile(pass_path, truncated_pass.c_str());
  }

  bssl::UniquePtr<std::string> source(
      new std::string(std::string("file:") + pass_path));
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on truncated file";

  // Test file exceeding maximum length
  {
    std::string long_pass(PEM_BUFSIZE + 10, 'B');
    WriteTestFile(pass_path, long_pass.c_str());
  }

  source.reset(new std::string(std::string("file:") + pass_path));
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on too long file content";

  // Test empty file
  {
    WriteTestFile(pass_path, "");
  }

  source.reset(new std::string(std::string("file:") + pass_path));
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on empty file";

  // Test file with only newlines - should succeed with empty password (like
  // OpenSSL)
  {
    WriteTestFile(pass_path, "\n\n\n", true);  // preserve_newlines = true
  }

  source.reset(new std::string(std::string("file:") + pass_path));
  bool result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed on newline-only file";
  EXPECT_TRUE(source->empty())
      << "Password should be empty from newline-only file";

  // Test file at buffer size - 1 with newline (should not trigger truncation)
  {
    std::string non_truncated_pass(PEM_BUFSIZE - 2, 'C');
    std::string content = non_truncated_pass + "\n";
    WriteTestFile(pass_path, content.c_str(),
                  true);  // preserve_newlines = true
  }

  source.reset(new std::string(std::string("file:") + pass_path));
  result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result)
      << "Should succeed when file is at max length but has newline";
  EXPECT_EQ(source->length(), static_cast<size_t>(PEM_BUFSIZE - 2))
      << "Password should not include newline and should be max length - 2";
}


TEST_F(PassUtilTest, EnvVarEdgeCases) {
  // Test empty environment variable
  SetTestEnvVar("TEST_EMPTY_PASSWORD", "");

  bssl::UniquePtr<std::string> source(
      new std::string("env:TEST_EMPTY_PASSWORD"));
  bool result = pass_util::ExtractPassword(source);
  EXPECT_FALSE(result) << "Should fail on empty environment variable";

  // Test maximum length environment variable
  std::string long_pass(PEM_BUFSIZE + 10, 'B');
  SetTestEnvVar("TEST_LONG_PASSWORD", long_pass.c_str());

  source.reset(new std::string("env:TEST_LONG_PASSWORD"));
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on too long environment variable";

  // Test non-existent environment variable
  source.reset(new std::string("env:NON_EXISTENT_VAR_NAME_12345"));
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on non-existent environment variable";

  UnsetTestEnvVar("TEST_EMPTY_PASSWORD");
  UnsetTestEnvVar("TEST_LONG_PASSWORD");
}

TEST_F(PassUtilTest, DirectPasswordEdgeCases) {
  // Test maximum length direct password
  std::string long_pass = "pass:" + std::string(PEM_BUFSIZE + 10, 'C');
  bssl::UniquePtr<std::string> source(new std::string(long_pass));
  EXPECT_FALSE(pass_util::ExtractPassword(source))
      << "Should fail on too long direct password";

  // Test empty direct password
  source.reset(new std::string("pass:"));
  bool result = pass_util::ExtractPassword(source);
  EXPECT_TRUE(result) << "Should succeed with empty direct password";
  EXPECT_TRUE(source->empty()) << "Password should be empty";

  // Test invalid format strings
  const char *invalid_formats[] = {
      "pass",           // Missing colon
      "pass:test:123",  // Multiple colons
      ":password",      // Missing prefix
      "invalid:pass",   // Invalid prefix
      "file:",          // Empty file path
      "env:",           // Empty environment variable
      "",               // Empty string
  };

  for (const char *fmt : invalid_formats) {
    source.reset(new std::string(fmt));
    EXPECT_FALSE(pass_util::ExtractPassword(source))
        << "Should fail on invalid format: " << fmt;
  }
}

TEST_F(PassUtilTest, SensitiveStringDeleter) {
  const char *test_password = "sensitive_data_to_be_cleared";
  std::string *str = new std::string(test_password);

  std::string original_content = *str;

  ASSERT_EQ(original_content, test_password)
      << "Failed to set up test password";

  const char *buffer_ptr = str->data();

  ASSERT_EQ(memcmp(buffer_ptr, test_password, str->length()), 0)
      << "Buffer doesn't contain expected password data";

  // Call the deleter
  pass_util::SensitiveStringDeleter(str);

  // The original string content should still be intact for comparison
  EXPECT_EQ(original_content, test_password)
      << "Original content was unexpectedly modified";
}

TEST_F(PassUtilTest, ExtractPasswordsDifferentFiles) {
  bssl::UniquePtr<std::string> passin(
      new std::string(std::string("file:") + pass_path));
  bssl::UniquePtr<std::string> passout(
      new std::string(std::string("file:") + pass_path2));

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(*passin, "testpassword");
  EXPECT_EQ(*passout, "anotherpassword");
}

TEST_F(PassUtilTest, ExtractPasswordsSameFile) {
  // Create file with two lines
  WriteTestFile(pass_path, "firstpassword\nsecondpassword\n", true);

  bssl::UniquePtr<std::string> passin(
      new std::string(std::string("file:") + pass_path));
  bssl::UniquePtr<std::string> passout(
      new std::string(std::string("file:") + pass_path));

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(*passin, "firstpassword");
  EXPECT_EQ(*passout, "secondpassword");
}

TEST_F(PassUtilTest, ExtractPasswordsMixedSources) {
  // Test file + environment variable
  bssl::UniquePtr<std::string> passin(
      new std::string(std::string("file:") + pass_path));
  bssl::UniquePtr<std::string> passout(
      new std::string("env:TEST_PASSWORD_ENV"));

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(*passin, "testpassword");
  EXPECT_EQ(*passout, "envpassword");

  // Test direct password + file
  passin.reset(new std::string("pass:directpass"));
  passout.reset(new std::string(std::string("file:") + pass_path2));

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(*passin, "directpass");
  EXPECT_EQ(*passout, "anotherpassword");
}

TEST_F(PassUtilTest, ExtractPasswordsEmptyPasswords) {
  // Both empty
  bssl::UniquePtr<std::string> passin(new std::string(""));
  bssl::UniquePtr<std::string> passout(new std::string(""));

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_TRUE(passin->empty());
  EXPECT_TRUE(passout->empty());

  // One empty, one with password
  passin.reset(new std::string(""));
  passout.reset(new std::string("pass:onlypassout"));

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_TRUE(passin->empty());
  EXPECT_EQ(*passout, "onlypassout");

  // Reverse: one with password, one empty
  passin.reset(new std::string("pass:onlypassin"));
  passout.reset(new std::string(""));

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(*passin, "onlypassin");
  EXPECT_TRUE(passout->empty());
}

TEST_F(PassUtilTest, ExtractPasswordsErrorCases) {
  // Invalid passin format
  bssl::UniquePtr<std::string> passin(new std::string("invalid:format"));
  bssl::UniquePtr<std::string> passout(new std::string("pass:validpass"));

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // Invalid passout format
  passin.reset(new std::string("pass:validpass"));
  passout.reset(new std::string("invalid:format"));

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // Both invalid formats
  passin.reset(new std::string("invalid1:format"));
  passout.reset(new std::string("invalid2:format"));

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // Null UniquePtr objects
  bssl::UniquePtr<std::string> null_passin;
  bssl::UniquePtr<std::string> null_passout;

  EXPECT_FALSE(pass_util::ExtractPasswords(null_passin, null_passout));

  // One null, one valid
  passin.reset(new std::string("pass:valid"));
  EXPECT_FALSE(pass_util::ExtractPasswords(passin, null_passout));
}

TEST_F(PassUtilTest, ExtractPasswordsFileErrors) {
  // Non-existent file for passin
  bssl::UniquePtr<std::string> passin(
      new std::string("file:/non/existent/file1"));
  bssl::UniquePtr<std::string> passout(new std::string("pass:validpass"));

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // Non-existent file for passout
  passin.reset(new std::string("pass:validpass"));
  passout.reset(new std::string("file:/non/existent/file2"));

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // Same non-existent file for both
  passin.reset(new std::string("file:/non/existent/samefile"));
  passout.reset(new std::string("file:/non/existent/samefile"));

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));
}

TEST_F(PassUtilTest, ExtractPasswordsSameFileEdgeCases) {
  // File with only one line (passout should fail)
  WriteTestFile(pass_path, "onlyoneline", false);

  bssl::UniquePtr<std::string> passin(
      new std::string(std::string("file:") + pass_path));
  bssl::UniquePtr<std::string> passout(
      new std::string(std::string("file:") + pass_path));

  EXPECT_FALSE(pass_util::ExtractPasswords(passin, passout));

  // File with empty second line
  WriteTestFile(pass_path, "firstline\n\n", true);

  passin.reset(new std::string(std::string("file:") + pass_path));
  passout.reset(new std::string(std::string("file:") + pass_path));

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(*passin, "firstline");
  EXPECT_TRUE(passout->empty());

  // File with multiple lines (should only read first two)
  WriteTestFile(pass_path, "line1\nline2\nline3\nline4\n", true);

  passin.reset(new std::string(std::string("file:") + pass_path));
  passout.reset(new std::string(std::string("file:") + pass_path));

  EXPECT_TRUE(pass_util::ExtractPasswords(passin, passout));
  EXPECT_EQ(*passin, "line1");
  EXPECT_EQ(*passout, "line2");
}
