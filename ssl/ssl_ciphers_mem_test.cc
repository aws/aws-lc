// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <gtest/gtest.h>

#include <openssl/err.h>
#include <openssl/mem.h>
#include <openssl/ssl.h>

#include <cassert>
#include <cstdlib>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "internal.h"

BSSL_NAMESPACE_BEGIN
namespace {

struct AllocationState {
  bool armed = false;
  size_t count = 0;
  size_t reallocations = 0;
  size_t fail_at = 0;
  bool failed = false;
};

AllocationState g_allocations;

bool ShouldFailAllocation() {
  if (!g_allocations.armed) {
    return false;
  }
  g_allocations.count++;
  if (g_allocations.count != g_allocations.fail_at) {
    return false;
  }
  g_allocations.failed = true;
  return true;
}

void *TestMalloc(size_t size, const char *, int) {
  return ShouldFailAllocation() ? nullptr : std::malloc(size == 0 ? 1 : size);
}

void *TestRealloc(void *ptr, size_t size, const char *, int) {
  if (g_allocations.armed) {
    g_allocations.reallocations++;
  }
  return ShouldFailAllocation() ? nullptr
                                : std::realloc(ptr, size == 0 ? 1 : size);
}

void TestFree(void *ptr, const char *, int) { std::free(ptr); }

// The hooks are process-global and can only be installed once. Install them
// before main so that every |OPENSSL_malloc| in the process, including those in
// |CRYPTO_library_init| and the FIPS self-tests, uses the same allocator. A
// block from the default allocator carries a size prefix that |TestFree| and
// |TestRealloc| would not strip. |CRYPTO_set_mem_functions| only stores the
// three pointers, so running it during static initialization is safe.
const int g_mem_functions_installed =
    CRYPTO_set_mem_functions(TestMalloc, TestRealloc, TestFree);

class ScopedAllocationFailure {
 public:
  // Zero counts allocations without failing any of them.
  explicit ScopedAllocationFailure(size_t fail_at) {
    assert(!g_allocations.armed);
    g_allocations.count = 0;
    g_allocations.reallocations = 0;
    g_allocations.fail_at = fail_at;
    g_allocations.failed = false;
    g_allocations.armed = true;
  }
  ~ScopedAllocationFailure() { g_allocations.armed = false; }

  ScopedAllocationFailure(const ScopedAllocationFailure &) = delete;
  ScopedAllocationFailure &operator=(const ScopedAllocationFailure &) = delete;

  size_t allocation_count() const { return g_allocations.count; }
  size_t reallocation_count() const { return g_allocations.reallocations; }
  bool failed() const { return g_allocations.failed; }
};

using CipherPolicy = std::vector<std::pair<uint32_t, bool>>;

const char kInitialTLS13Rule[] =
    "[TLS_AES_128_GCM_SHA256|TLS_CHACHA20_POLY1305_SHA256]";
const char kInitialLegacyRule[] =
    "[ECDHE-RSA-AES128-GCM-SHA256|ECDHE-ECDSA-AES128-GCM-SHA256]";
// Merging two TLS 1.3 suites with these two legacy suites outgrows a new
// stack's initial capacity, so realloc is exercised as well as malloc. The test
// records rather than asserts this, as the capacity is a stack implementation
// detail.
const char kReplacementLegacyRule[] =
    "ECDHE-RSA-AES256-GCM-SHA384:ECDHE-ECDSA-AES256-GCM-SHA384";
const CipherPolicy kInitialTLS13Policy = {
    {TLS1_CK_AES_128_GCM_SHA256, true},
    {TLS1_CK_CHACHA20_POLY1305_SHA256, false},
};
const CipherPolicy kInitialLegacyPolicy = {
    {TLS1_CK_ECDHE_RSA_WITH_AES_128_GCM_SHA256, true},
    {TLS1_CK_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, false},
};

CipherPolicy CombinePolicies(const CipherPolicy &tls13,
                             const CipherPolicy &legacy) {
  CipherPolicy combined = tls13;
  combined.insert(combined.end(), legacy.begin(), legacy.end());
  return combined;
}

std::vector<uint32_t> CipherIDs(const STACK_OF(SSL_CIPHER) *ciphers) {
  std::vector<uint32_t> ids;
  for (size_t i = 0; i < sk_SSL_CIPHER_num(ciphers); i++) {
    ids.push_back(SSL_CIPHER_get_id(sk_SSL_CIPHER_value(ciphers, i)));
  }
  return ids;
}

CipherPolicy SnapshotPolicy(const SSLCipherPreferenceList *list) {
  CipherPolicy policy;
  if (list == nullptr) {
    return policy;
  }
  EXPECT_NE(nullptr, list->ciphers.get());
  const size_t num = sk_SSL_CIPHER_num(list->ciphers.get());
  if (num != 0) {
    EXPECT_NE(nullptr, list->in_group_flags);
    if (list->in_group_flags == nullptr) {
      return policy;
    }
  }
  for (size_t i = 0; i < num; i++) {
    policy.emplace_back(
        SSL_CIPHER_get_id(sk_SSL_CIPHER_value(list->ciphers.get(), i)),
        list->in_group_flags[i]);
  }
  return policy;
}

const SSLCipherPreferenceList *CombinedPolicy(const SSL_CTX *ctx,
                                              const SSL *ssl) {
  return ssl != nullptr && ssl->config->cipher_list
             ? ssl->config->cipher_list.get()
             : ctx->cipher_list.get();
}

const SSLCipherPreferenceList *TLS13Policy(const SSL_CTX *ctx, const SSL *ssl) {
  // Do not fall back to the context here: the stored policy must also survive
  // a failed setter, even when the public combined list still looks correct.
  return ssl != nullptr ? ssl->config->tls13_cipher_list.get()
                        : ctx->tls13_cipher_list.get();
}

void ExpectPolicies(const SSL_CTX *ctx, const SSL *ssl,
                    const CipherPolicy &combined, const CipherPolicy &tls13) {
  SCOPED_TRACE(ssl == nullptr ? "SSL_CTX" : "SSL");
  std::vector<uint32_t> expected_ids;
  for (const auto &cipher : combined) {
    expected_ids.push_back(cipher.first);
  }
  EXPECT_EQ(expected_ids, CipherIDs(ssl != nullptr ? SSL_get_ciphers(ssl)
                                                   : SSL_CTX_get_ciphers(ctx)));
  EXPECT_EQ(combined, SnapshotPolicy(CombinedPolicy(ctx, ssl)));
  EXPECT_NE(nullptr, TLS13Policy(ctx, ssl));
  EXPECT_EQ(tls13, SnapshotPolicy(TLS13Policy(ctx, ssl)));
}

enum class Target { kContext, kInheritedConnection, kConfiguredConnection };
enum class Setter { kTLS13, kLegacy, kStrictLegacy };

struct SetterCase {
  const char *name;
  Setter setter;
  const char *rule;
};

const SetterCase kSetterCases[] = {
    {"TLS13Replacement", Setter::kTLS13, "TLS_AES_256_GCM_SHA384"},
    {"TLS13Empty", Setter::kTLS13, ""},
    {"LegacyReplacement", Setter::kLegacy, kReplacementLegacyRule},
    {"LegacyEmpty", Setter::kLegacy, ""},
    {"StrictLegacyReplacement", Setter::kStrictLegacy, kReplacementLegacyRule},
};

int CallSetter(SSL_CTX *ctx, SSL *ssl, const SetterCase &test) {
  switch (test.setter) {
    case Setter::kTLS13:
      return ssl != nullptr ? SSL_set_ciphersuites(ssl, test.rule)
                            : SSL_CTX_set_ciphersuites(ctx, test.rule);
    case Setter::kLegacy:
      return ssl != nullptr ? SSL_set_cipher_list(ssl, test.rule)
                            : SSL_CTX_set_cipher_list(ctx, test.rule);
    case Setter::kStrictLegacy:
      return ssl != nullptr ? SSL_set_strict_cipher_list(ssl, test.rule)
                            : SSL_CTX_set_strict_cipher_list(ctx, test.rule);
  }
  std::abort();
}

using TestParam = std::tuple<Target, SetterCase>;

class SSLCipherAllocationTest : public testing::TestWithParam<TestParam> {
 protected:
  void SetUp() override {
    ASSERT_EQ(1, g_mem_functions_installed);
    ASSERT_FALSE(g_allocations.armed);
    ERR_clear_error();
  }
};

TEST_P(SSLCipherAllocationTest, SetterIsAtomic) {
  const Target target = std::get<0>(GetParam());
  const SetterCase &test = std::get<1>(GetParam());
  const CipherPolicy initial_combined =
      CombinePolicies(kInitialTLS13Policy, kInitialLegacyPolicy);
  CipherPolicy expected_tls13 = kInitialTLS13Policy;
  CipherPolicy expected_legacy = kInitialLegacyPolicy;
  if (test.setter == Setter::kTLS13) {
    expected_tls13 = test.rule[0] == '\0'
                         ? CipherPolicy{}
                         : CipherPolicy{{TLS1_CK_AES_256_GCM_SHA384, false}};
  } else {
    expected_legacy =
        test.rule[0] == '\0'
            ? CipherPolicy{}
            : CipherPolicy{
                  {TLS1_CK_ECDHE_RSA_WITH_AES_256_GCM_SHA384, false},
                  {TLS1_CK_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384, false}};
  }
  const CipherPolicy expected_combined =
      CombinePolicies(expected_tls13, expected_legacy);

  // Count the successful path, then fail each malloc/realloc in turn on a fresh
  // object. Do not hard-code allocation counts, which may vary between builds.
  size_t num_allocations = 0;
  for (size_t fail_at = 0; fail_at <= num_allocations; fail_at++) {
    SCOPED_TRACE(testing::Message()
                 << "allocation " << fail_at << " of " << num_allocations);
    UniquePtr<SSL_CTX> ctx(SSL_CTX_new(TLS_method()));
    ASSERT_TRUE(ctx);
    ASSERT_EQ(1, SSL_CTX_set_cipher_list(ctx.get(), kInitialLegacyRule));
    ASSERT_EQ(1, SSL_CTX_set_ciphersuites(ctx.get(), kInitialTLS13Rule));
    UniquePtr<SSL> ssl;
    if (target != Target::kContext) {
      ssl.reset(SSL_new(ctx.get()));
      ASSERT_TRUE(ssl);
      if (target == Target::kConfiguredConnection) {
        ASSERT_EQ(1, SSL_set_cipher_list(ssl.get(), kInitialLegacyRule));
        ASSERT_EQ(1, SSL_set_ciphersuites(ssl.get(), kInitialTLS13Rule));
      }
    }
    ExpectPolicies(ctx.get(), ssl.get(), initial_combined, kInitialTLS13Policy);
    const CipherPolicy before_combined =
        SnapshotPolicy(CombinedPolicy(ctx.get(), ssl.get()));
    const CipherPolicy before_tls13 =
        SnapshotPolicy(TLS13Policy(ctx.get(), ssl.get()));
    const bool had_local_list = ssl && ssl->config->cipher_list;

    ERR_clear_error();
    int ret;
    size_t count, reallocations;
    bool failed;
    {
      ScopedAllocationFailure failure(fail_at);
      ret = CallSetter(ctx.get(), ssl.get(), test);
      count = failure.allocation_count();
      reallocations = failure.reallocation_count();
      failed = failure.failed();
    }
    // Assertions, snapshots, retries, and object destruction all run after the
    // guard disables failures. The hooks never affect gtest's allocations.
    if (fail_at == 0) {
      ASSERT_FALSE(failed);
      ASSERT_EQ(1, ret);
      ASSERT_GT(count, 0u);
      num_allocations = count;
      RecordProperty("allocation_points", std::to_string(num_allocations));
      RecordProperty("reallocation_points", std::to_string(reallocations));
    } else {
      EXPECT_TRUE(failed);
      EXPECT_EQ(0, ret);
      ExpectPolicies(ctx.get(), ssl.get(), before_combined, before_tls13);
      EXPECT_EQ(had_local_list, ssl && ssl->config->cipher_list);
      if (ssl) {
        ExpectPolicies(ctx.get(), nullptr, initial_combined,
                       kInitialTLS13Policy);
      }
      ERR_clear_error();
      ASSERT_EQ(1, CallSetter(ctx.get(), ssl.get(), test));
    }
    ExpectPolicies(ctx.get(), ssl.get(), expected_combined, expected_tls13);
    if (ssl) {
      ExpectPolicies(ctx.get(), nullptr, initial_combined, kInitialTLS13Policy);
    }
    ERR_clear_error();
  }
}

std::string TestName(const testing::TestParamInfo<TestParam> &info) {
  const char *target = "";
  switch (std::get<0>(info.param)) {
    case Target::kContext:
      target = "Context";
      break;
    case Target::kInheritedConnection:
      target = "InheritedConnection";
      break;
    case Target::kConfiguredConnection:
      target = "ConfiguredConnection";
      break;
  }
  return std::string(target) + std::get<1>(info.param).name;
}

INSTANTIATE_TEST_SUITE_P(
    Setters, SSLCipherAllocationTest,
    testing::Combine(testing::Values(Target::kContext,
                                     Target::kInheritedConnection,
                                     Target::kConfiguredConnection),
                     testing::ValuesIn(kSetterCases)),
    TestName);

}  // namespace
BSSL_NAMESPACE_END
