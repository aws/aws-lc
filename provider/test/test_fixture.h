// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_TEST_FIXTURE_H
#define AWSLC_PROVIDER_TEST_FIXTURE_H

// The fixture every provider test builds on.
//
// Each test gets its own OSSL_LIB_CTX rather than the process-global default, so
// cells are isolated and a test can assert precisely which providers are
// present. The provider is loaded from the build tree, so the suite runs without
// an install step.

#include <gtest/gtest.h>

#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <openssl/provider.h>

#include <memory>

namespace awslc_provider_test {

// The directory holding the freshly built provider, supplied by CMake.
#ifndef AWSLC_PROVIDER_MODULE_DIR
#error "AWSLC_PROVIDER_MODULE_DIR must be defined by the build"
#endif

// The name the provider is loaded and attributed under. Fetch queries and
// OSSL_PROVIDER_get0_name results are compared against this.
#define AWSLC_TEST_PROVIDER_NAME "awslc"

// A preference, not a requirement: anything the provider does not implement
// falls through to whichever other provider does. The whole safety story rests
// on the leading '?', so tests that assert fallthrough use exactly this string.
#define AWSLC_TEST_PREFER "?provider=awslc"

// A hard requirement, used only to prove attribution: a fetch that succeeds
// under this string cannot have been served by anyone else.
#define AWSLC_TEST_REQUIRE "provider=awslc"

static const char *const kProviderName = AWSLC_TEST_PROVIDER_NAME;
static const char *const kPreferAwslc = AWSLC_TEST_PREFER;
static const char *const kRequireAwslc = AWSLC_TEST_REQUIRE;

struct LibCtxDeleter {
  void operator()(OSSL_LIB_CTX *ctx) const { OSSL_LIB_CTX_free(ctx); }
};
struct ProviderDeleter {
  void operator()(OSSL_PROVIDER *p) const { OSSL_PROVIDER_unload(p); }
};
struct MdDeleter {
  void operator()(EVP_MD *md) const { EVP_MD_free(md); }
};
struct MdCtxDeleter {
  void operator()(EVP_MD_CTX *ctx) const { EVP_MD_CTX_free(ctx); }
};

using LibCtxPtr = std::unique_ptr<OSSL_LIB_CTX, LibCtxDeleter>;
using ProviderPtr = std::unique_ptr<OSSL_PROVIDER, ProviderDeleter>;
using MdPtr = std::unique_ptr<EVP_MD, MdDeleter>;
using MdCtxPtr = std::unique_ptr<EVP_MD_CTX, MdCtxDeleter>;

// Loads the provider into a private libctx, alongside the default provider.
// Keeping default loaded is not incidental: it is the fallback leg that makes
// '?provider=awslc' safe, so the fixture reproduces the deployed arrangement
// rather than a provider-only one.
class ProviderTest : public ::testing::Test {
 protected:
  void SetUp() override {
    libctx_.reset(OSSL_LIB_CTX_new());
    ASSERT_TRUE(libctx_) << "could not create a library context";

    ASSERT_TRUE(OSSL_PROVIDER_set_default_search_path(
        libctx_.get(), AWSLC_PROVIDER_MODULE_DIR))
        << "could not point OpenSSL at " << AWSLC_PROVIDER_MODULE_DIR;

    awslc_.reset(OSSL_PROVIDER_load(libctx_.get(), kProviderName));
    ASSERT_TRUE(awslc_) << "could not load the provider from "
                        << AWSLC_PROVIDER_MODULE_DIR
                        << "; OSSL_provider_init may have failed";

    default_.reset(OSSL_PROVIDER_load(libctx_.get(), "default"));
    ASSERT_TRUE(default_) << "could not load the default provider";
  }

  void TearDown() override {
    default_.reset();
    awslc_.reset();
    libctx_.reset();
  }

  OSSL_LIB_CTX *libctx() { return libctx_.get(); }
  OSSL_PROVIDER *awslc() { return awslc_.get(); }

 private:
  LibCtxPtr libctx_;
  ProviderPtr awslc_;
  ProviderPtr default_;
};

}  // namespace awslc_provider_test

#endif  // AWSLC_PROVIDER_TEST_FIXTURE_H
