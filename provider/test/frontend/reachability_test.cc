// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// The provider-wide inventory of advertised algorithms and their attributed
// public fetch paths.

#include "test/test_fixture.h"

#include <openssl/core_dispatch.h>
#include <openssl/evp.h>

#include <algorithm>
#include <cctype>
#include <string>
#include <vector>

namespace awslc_provider_test {
namespace {

struct ReachabilityCell {
  int operation;
  const char *name;
};

// One attributed test cell per registry row. Duplicates stay duplicated so the
// comparison below detects both missing coverage and accidental registrations.
constexpr ReachabilityCell kReachabilityCells[] = {
    {OSSL_OP_DIGEST, "SHA2-224"},
    {OSSL_OP_DIGEST, "SHA2-256"},
    {OSSL_OP_DIGEST, "SHA2-384"},
    {OSSL_OP_DIGEST, "SHA2-512"},
    {OSSL_OP_DIGEST, "SHA2-512/224"},
    {OSSL_OP_DIGEST, "SHA2-512/256"},
};

std::string ReachabilityKey(int operation, const std::string &name) {
  return std::to_string(operation) + ":" + name;
}

TEST_F(ProviderTest, AdvertisedAlgorithmsMatchReachabilityCells) {
  std::vector<std::string> advertised;
  for (int operation = 1; operation <= OSSL_OP__HIGHEST; operation++) {
    int no_cache = 0;
    const OSSL_ALGORITHM *algorithms =
        OSSL_PROVIDER_query_operation(awslc(), operation, &no_cache);

    for (const OSSL_ALGORITHM *algorithm = algorithms;
         algorithm != nullptr && algorithm->algorithm_names != nullptr;
         algorithm++) {
      const std::string names = algorithm->algorithm_names;
      const std::string name = names.substr(0, names.find(':'));
      advertised.push_back(ReachabilityKey(operation, name));
    }

    OSSL_PROVIDER_unquery_operation(awslc(), operation, algorithms);
  }

  std::vector<std::string> covered;
  for (const ReachabilityCell &cell : kReachabilityCells) {
    covered.push_back(ReachabilityKey(cell.operation, cell.name));
  }

  std::sort(advertised.begin(), advertised.end());
  std::sort(covered.begin(), covered.end());
  EXPECT_EQ(advertised, covered);
}

class ReachabilityTest
    : public ProviderTest,
      public ::testing::WithParamInterface<ReachabilityCell> {};

TEST_P(ReachabilityTest, IsReachableAndAttributed) {
  const ReachabilityCell &cell = GetParam();

  switch (cell.operation) {
    case OSSL_OP_DIGEST: {
      MdPtr md(EVP_MD_fetch(libctx(), cell.name, kRequireAwslc));
      ASSERT_TRUE(md) << cell.name << " was not reachable";
      EXPECT_STREQ(kProviderName,
                   OSSL_PROVIDER_get0_name(EVP_MD_get0_provider(md.get())));
      break;
    }
    default:
      FAIL() << "operation " << cell.operation
             << " has no attributed reachability handler";
  }
}

std::string ReachabilityName(
    const testing::TestParamInfo<ReachabilityCell> &info) {
  std::string name =
      "Op" + std::to_string(info.param.operation) + "_" + info.param.name;
  for (char &c : name) {
    if (!isalnum(static_cast<unsigned char>(c))) {
      c = '_';
    }
  }
  return name;
}

INSTANTIATE_TEST_SUITE_P(Provider, ReachabilityTest,
                         testing::ValuesIn(kReachabilityCells),
                         ReachabilityName);

}  // namespace
}  // namespace awslc_provider_test
