// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <openssl/base.h>
#include "../tool/internal.h"
#include <openssl/evp.h>
#include <openssl/err.h>
#include <openssl/bio.h>
#include <openssl/rsa.h>
#include <string.h>
#include <stdio.h>


#include <gtest/gtest.h>
#include <openssl/pem.h>
#include "internal.h"
#include "test_util.h"
#include "../crypto/test/test_util.h"











struct SubjectNameTestCase {
  std::string input;
  bool expect_success;
  int expected_entry_count;
  std::vector<std::string> expected_values;
};
class SubjectNameTest : public testing::TestWithParam<SubjectNameTestCase> {
 protected:
  static std::string GetEntryValue(X509_NAME* name, int index) {
    unsigned char* tmp;
    X509_NAME_ENTRY* entry = X509_NAME_get_entry(name, index);
    int len = ASN1_STRING_to_UTF8(&tmp, X509_NAME_ENTRY_get_data(entry));
    std::string result;
    if (len > 0) {
      result.assign(reinterpret_cast<char*>(tmp), len);
    }
    OPENSSL_free(tmp);
    return result;
  }
};

INSTANTIATE_TEST_SUITE_P(
    SubjectNameTests,
    SubjectNameTest,
    testing::Values(
        // Valid subject with multiple fields
        SubjectNameTestCase{
            "/C=US/ST=California/O=Example/CN=test.com",
            true,
            4,
            {"US", "California", "Example", "test.com"}
        },
        // Escaped characters
        SubjectNameTestCase{
            "/CN=test\\/example\\.com",
            true,
            1,
            {"test/example.com"}
        },
        // Missing leading slash
        SubjectNameTestCase{
            "CN=test.com",
            false,
            0,
            {}
        },
        // Missing equals sign
        SubjectNameTestCase{
            "/CNtest.com",
            false,
            0,
            {}
        },
        // Empty value
        SubjectNameTestCase{
            "/CN=/O=test",
            true,
            1,
            {"test"}
        },
        // Unknown attribute
        SubjectNameTestCase{
            "/UNKNOWN=test/CN=example.com",
            true,
            1,
            {"example.com"}
        },
        // Empty subject
        SubjectNameTestCase{
            "/",
            true,
            0,
            {}
        }
));

TEST_P(SubjectNameTest, ParseSubjectName) {
  const SubjectNameTestCase& test_case = GetParam();
  std::string mutable_input = test_case.input;  // Create mutable copy

  X509_NAME* name = parse_subject_name(mutable_input);

  if (!test_case.expect_success) {
    EXPECT_EQ(name, nullptr);
    return;
  }

  ASSERT_NE(name, nullptr);
  EXPECT_EQ(X509_NAME_entry_count(name), test_case.expected_entry_count);

  for (size_t i = 0; i < test_case.expected_values.size(); ++i) {
    EXPECT_EQ(GetEntryValue(name, i), test_case.expected_values[i]);
  }

  X509_NAME_free(name);
}





