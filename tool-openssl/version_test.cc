// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>
#include <openssl/crypto.h>

#include <string>

#include "internal.h"

TEST(VersionTest, FIPSStatus) {
  testing::internal::CaptureStdout();
  const int result = VersionTool({"-fips"});
  const std::string output = testing::internal::GetCapturedStdout();
  EXPECT_EQ(kToolExitSuccess, result);
  std::string expected = std::string(OPENSSL_VERSION_TEXT) + "\nFIPS: " +
                         (FIPS_mode() ? "enabled\n" : "disabled\n");
#if defined(BORINGSSL_FIPS_140_3)
  if (FIPS_mode()) {
    EXPECT_STREQ("AWSLCCrypto", FIPS_module_name());
    expected += std::string("FIPS module: ") + FIPS_module_name() + " module " +
                std::to_string(FIPS_version()) + "\n";
  }
#endif
  EXPECT_EQ(expected, output);
}
