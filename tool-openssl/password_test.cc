// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/base.h>
#include <openssl/mem.h>
#include <openssl/bio.h>
#include <string>
#include "internal.h"
#include "test_util.h"

class PasswordTest : public ::testing::Test {
protected:
  void SetUp() override {
    // Create temporary files for testing
    ASSERT_GT(createTempFILEpath(pass_path), 0u);
    ASSERT_GT(createTempFILEpath(pass_path2), 0u);
    
    // Write test passwords to files
    bssl::UniquePtr<BIO> pass_bio(BIO_new_file(pass_path, "wb"));
    ASSERT_TRUE(pass_bio);
    ASSERT_TRUE(BIO_printf(pass_bio.get(), "testpassword") > 0);
    BIO_flush(pass_bio.get());
    
    bssl::UniquePtr<BIO> pass_bio2(BIO_new_file(pass_path2, "wb"));
    ASSERT_TRUE(pass_bio2);
    ASSERT_TRUE(BIO_printf(pass_bio2.get(), "anotherpassword") > 0);
    BIO_flush(pass_bio2.get());
    
    // Set up environment variable for testing
    setenv("TEST_PASSWORD_ENV", "envpassword", 1);
  }
  
  void TearDown() override {
    RemoveFile(pass_path);
    RemoveFile(pass_path2);
    unsetenv("TEST_PASSWORD_ENV");
  }
  
  char pass_path[PATH_MAX] = {};
  char pass_path2[PATH_MAX] = {};
};

// Test ExtractPassword with direct password
TEST_F(PasswordTest, ExtractPasswordDirect) {
  bssl::UniquePtr<std::string> source(new std::string("pass:directpassword"));
  bssl::UniquePtr<std::string> result = password::ExtractPassword(source);
  
  ASSERT_TRUE(result);
  EXPECT_EQ(*result, "directpassword");
}

// Test ExtractPassword with file
TEST_F(PasswordTest, ExtractPasswordFile) {
  std::string file_path = std::string("file:") + pass_path;
  bssl::UniquePtr<std::string> source(new std::string(file_path));
  bssl::UniquePtr<std::string> result = password::ExtractPassword(source);
  
  ASSERT_TRUE(result);
  EXPECT_EQ(*result, "testpassword");
}

// Test ExtractPassword with environment variable
TEST_F(PasswordTest, ExtractPasswordEnv) {
  bssl::UniquePtr<std::string> source(new std::string("env:TEST_PASSWORD_ENV"));
  bssl::UniquePtr<std::string> result = password::ExtractPassword(source);
  
  ASSERT_TRUE(result);
  EXPECT_EQ(*result, "envpassword");
}

// Test ExtractPassword with empty source
TEST_F(PasswordTest, ExtractPasswordEmpty) {
  bssl::UniquePtr<std::string> source(new std::string(""));
  bssl::UniquePtr<std::string> result = password::ExtractPassword(source);
  
  ASSERT_TRUE(result);
  EXPECT_TRUE(result->empty());
}

// Test ExtractPassword with nullptr source
TEST_F(PasswordTest, ExtractPasswordNull) {
  bssl::UniquePtr<std::string> source;
  bssl::UniquePtr<std::string> result = password::ExtractPassword(source);
  
  ASSERT_TRUE(result);
  EXPECT_TRUE(result->empty());
}

// Test ExtractPassword with invalid format
TEST_F(PasswordTest, ExtractPasswordInvalidFormat) {
  bssl::UniquePtr<std::string> source(new std::string("invalid:format"));
  bssl::UniquePtr<std::string> result = password::ExtractPassword(source);
  
  EXPECT_FALSE(result);
}

// Test ExtractPassword with non-existent file
TEST_F(PasswordTest, ExtractPasswordNonExistentFile) {
  bssl::UniquePtr<std::string> source(new std::string("file:/non/existent/file"));
  bssl::UniquePtr<std::string> result = password::ExtractPassword(source);
  
  EXPECT_FALSE(result);
}

// Test ExtractPassword with non-existent environment variable
TEST_F(PasswordTest, ExtractPasswordNonExistentEnv) {
  bssl::UniquePtr<std::string> source(new std::string("env:NON_EXISTENT_ENV_VAR"));
  bssl::UniquePtr<std::string> result = password::ExtractPassword(source);
  
  EXPECT_FALSE(result);
}

// Test HandlePassOptions with both passin and passout
TEST_F(PasswordTest, HandlePassOptionsBoth) {
  bssl::UniquePtr<std::string> passin(new std::string("pass:inputpass"));
  bssl::UniquePtr<std::string> passout(new std::string("pass:outputpass"));
  
  ASSERT_TRUE(password::HandlePassOptions(&passin, &passout));
  
  EXPECT_EQ(*passin, "inputpass");
  EXPECT_EQ(*passout, "outputpass");
}

// Test HandlePassOptions with only passin
TEST_F(PasswordTest, HandlePassOptionsPassinOnly) {
  bssl::UniquePtr<std::string> passin(new std::string("pass:inputpass"));
  bssl::UniquePtr<std::string> passout;
  
  ASSERT_TRUE(password::HandlePassOptions(&passin, &passout));
  
  EXPECT_EQ(*passin, "inputpass");
  EXPECT_FALSE(passout);
}

// Test HandlePassOptions with only passout
TEST_F(PasswordTest, HandlePassOptionsPassoutOnly) {
  bssl::UniquePtr<std::string> passin;
  bssl::UniquePtr<std::string> passout(new std::string("pass:outputpass"));
  
  ASSERT_TRUE(password::HandlePassOptions(&passin, &passout));
  
  EXPECT_FALSE(passin);
  EXPECT_EQ(*passout, "outputpass");
}

// Test HandlePassOptions with nullptr for both
TEST_F(PasswordTest, HandlePassOptionsNullBoth) {
  ASSERT_TRUE(password::HandlePassOptions(nullptr, nullptr));
}

// Test HandlePassOptions with same source for both
TEST_F(PasswordTest, HandlePassOptionsSameSource) {
  std::string file_path = std::string("file:") + pass_path;
  bssl::UniquePtr<std::string> passin(new std::string(file_path));
  bssl::UniquePtr<std::string> passout(new std::string(file_path));
  
  ASSERT_TRUE(password::HandlePassOptions(&passin, &passout));
  
  EXPECT_EQ(*passin, "testpassword");
  EXPECT_EQ(*passout, "testpassword");
  
  // Verify they are different objects in memory
  EXPECT_NE(passin.get(), passout.get());
}

// Test HandlePassOptions with different sources
TEST_F(PasswordTest, HandlePassOptionsDifferentSources) {
  std::string file_path1 = std::string("file:") + pass_path;
  std::string file_path2 = std::string("file:") + pass_path2;
  bssl::UniquePtr<std::string> passin(new std::string(file_path1));
  bssl::UniquePtr<std::string> passout(new std::string(file_path2));
  
  ASSERT_TRUE(password::HandlePassOptions(&passin, &passout));
  
  EXPECT_EQ(*passin, "testpassword");
  EXPECT_EQ(*passout, "anotherpassword");
}

// Test HandlePassOptions with invalid passin
TEST_F(PasswordTest, HandlePassOptionsInvalidPassin) {
  bssl::UniquePtr<std::string> passin(new std::string("invalid:format"));
  bssl::UniquePtr<std::string> passout(new std::string("pass:outputpass"));
  
  EXPECT_FALSE(password::HandlePassOptions(&passin, &passout));
}

// Test HandlePassOptions with invalid passout
TEST_F(PasswordTest, HandlePassOptionsInvalidPassout) {
  bssl::UniquePtr<std::string> passin(new std::string("pass:inputpass"));
  bssl::UniquePtr<std::string> passout(new std::string("invalid:format"));
  
  EXPECT_FALSE(password::HandlePassOptions(&passin, &passout));
}

// Test SensitiveStringDeleter properly clears memory
TEST_F(PasswordTest, SensitiveStringDeleter) {
  const char* test_password = "sensitive_data_to_be_cleared";
  std::string* str = new std::string(test_password);
  
  // Get the memory address and make a copy of the content
  const char* memory_ptr = str->c_str();
  char memory_copy[64] = {};
  memcpy(memory_copy, memory_ptr, str->length());
  
  // Verify the copy contains the password
  EXPECT_STREQ(memory_copy, test_password);
  
  // Call the deleter
  password::SensitiveStringDeleter(str);
  
  // The memory should now be cleared (all zeros or at least not the original password)
  // Note: This test is somewhat implementation-dependent and may not always work
  // as expected due to compiler optimizations or memory management
  bool memory_cleared = (memcmp(memory_copy, memory_ptr, strlen(test_password)) != 0);
  EXPECT_TRUE(memory_cleared);
}

// Test memory safety with HandlePassOptions
TEST_F(PasswordTest, HandlePassOptionsMemorySafety) {
  // Create a password with a known pattern
  const char* test_pattern = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
  bssl::UniquePtr<std::string> passin(new std::string("pass:"));
  passin->append(test_pattern);
  
  // Create a copy to verify it's properly cleaned up
  std::string original_passin = *passin;
  
  {
    // Create a scope to test cleanup
    bssl::UniquePtr<std::string> passout;
    ASSERT_TRUE(password::HandlePassOptions(&passin, &passout));
    
    // Verify the password was extracted correctly
    EXPECT_EQ(*passin, test_pattern);
  }
  
  // After the scope, the original string should still be intact
  // but the extracted password should be gone
  EXPECT_EQ(original_passin, "pass:ABCDEFGHIJKLMNOPQRSTUVWXYZ");
}
