// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// The provider-global surface: that the module loads, reports itself correctly,
// and declines every operation class, so fetches fall through to another
// provider rather than failing.

#include "test/test_fixture.h"

#include <openssl/core_names.h>
#include <openssl/evp.h>
#include <openssl/params.h>
#include <openssl/provider.h>

#include <string>

namespace awslc_provider_test {
namespace {

#ifndef AWSLC_PROVIDER_CONFIG_FILE
#error "AWSLC_PROVIDER_CONFIG_FILE must be defined by the build"
#endif

TEST_F(ProviderTest, Loads) {
  EXPECT_TRUE(OSSL_PROVIDER_available(libctx(), kProviderName));
  EXPECT_STREQ(kProviderName, OSSL_PROVIDER_get0_name(awslc()));
}

TEST_F(ProviderTest, ReportsSelfDescribingParams) {
  const char *name = nullptr;
  const char *version = nullptr;
  const char *buildinfo = nullptr;
  int status = 0;

  OSSL_PARAM params[] = {
      OSSL_PARAM_construct_utf8_ptr(OSSL_PROV_PARAM_NAME,
                                    const_cast<char **>(&name), 0),
      OSSL_PARAM_construct_utf8_ptr(OSSL_PROV_PARAM_VERSION,
                                    const_cast<char **>(&version), 0),
      OSSL_PARAM_construct_utf8_ptr(OSSL_PROV_PARAM_BUILDINFO,
                                    const_cast<char **>(&buildinfo), 0),
      OSSL_PARAM_construct_int(OSSL_PROV_PARAM_STATUS, &status),
      OSSL_PARAM_construct_end()};

  ASSERT_TRUE(OSSL_PROVIDER_get_params(awslc(), params));

  ASSERT_NE(nullptr, name);
  EXPECT_STREQ("AWS-LC Provider", name);
  ASSERT_NE(nullptr, version);

  // buildinfo is where the AWS-LC identity belongs. A consumer cannot otherwise
  // tell which AWS-LC is underneath, since our own version deliberately does not
  // say.
  ASSERT_NE(nullptr, buildinfo);
  EXPECT_NE(std::string::npos, std::string(buildinfo).find("AWS-LC"));

  EXPECT_EQ(1, status);
}

TEST_F(ProviderTest, DeclaresGettableParams) {
  const OSSL_PARAM *gettable = OSSL_PROVIDER_gettable_params(awslc());
  ASSERT_NE(nullptr, gettable);

  for (const char *key : {OSSL_PROV_PARAM_NAME, OSSL_PROV_PARAM_VERSION,
                          OSSL_PROV_PARAM_BUILDINFO, OSSL_PROV_PARAM_STATUS}) {
    EXPECT_NE(nullptr, OSSL_PARAM_locate_const(gettable, key))
        << "get_params answers " << key << " but does not advertise it";
  }
}

// An operation class the provider does not serve must return NULL from
// query_operation, which is what lets the fetch fall through to another provider
// instead of failing.
//
// Camellia rather than an algorithm we might serve later: AWS-LC is built
// OPENSSL_NO_CAMELLIA and OpenSSL's default provider does serve it
#define AWSLC_TEST_UNBACKED_CIPHER "CAMELLIA-256-CBC"

TEST_F(ProviderTest, DoesNotClaimUnimplementedOperations) {
  EVP_CIPHER *cipher =
      EVP_CIPHER_fetch(libctx(), AWSLC_TEST_UNBACKED_CIPHER, kRequireAwslc);
  EXPECT_EQ(nullptr, cipher)
      << "provider claimed " AWSLC_TEST_UNBACKED_CIPHER
         ", which AWS-LC does not implement";
  EVP_CIPHER_free(cipher);
}

// The other half of the same contract, and the more important half: an algorithm
// we decline must still resolve, served by default. This is what makes
// '?provider=awslc' safe to set system-wide.
TEST_F(ProviderTest, UnimplementedOperationsFallThroughToDefault) {
  EVP_CIPHER *cipher =
      EVP_CIPHER_fetch(libctx(), AWSLC_TEST_UNBACKED_CIPHER, kPreferAwslc);
  ASSERT_NE(nullptr, cipher) << "a declined cipher did not fall through";
  EXPECT_STREQ("default",
               OSSL_PROVIDER_get0_name(EVP_CIPHER_get0_provider(cipher)));
  EVP_CIPHER_free(cipher);
}

// Reproduce the deployed path: the config activates both providers and installs
// the optional awslc property as the libctx's default query. Fetches below pass
// no explicit property string, so both selection outcomes come from the config.
TEST(ProviderConfigTest, LoadsPreferenceAndFallback) {
  LibCtxPtr libctx(OSSL_LIB_CTX_new());
  ASSERT_TRUE(libctx);
  ASSERT_TRUE(OSSL_PROVIDER_set_default_search_path(
      libctx.get(), AWSLC_PROVIDER_MODULE_DIR));
  ASSERT_TRUE(
      OSSL_LIB_CTX_load_config(libctx.get(), AWSLC_PROVIDER_CONFIG_FILE));

  EXPECT_TRUE(OSSL_PROVIDER_available(libctx.get(), kProviderName));
  EXPECT_TRUE(OSSL_PROVIDER_available(libctx.get(), "default"));

  char *properties = EVP_get1_default_properties(libctx.get());
  ASSERT_NE(nullptr, properties);
  EXPECT_STREQ(kPreferAwslc, properties);
  OPENSSL_free(properties);

  MdPtr preferred(EVP_MD_fetch(libctx.get(), "SHA2-256", nullptr));
  ASSERT_TRUE(preferred);
  EXPECT_STREQ(
      kProviderName,
      OSSL_PROVIDER_get0_name(EVP_MD_get0_provider(preferred.get())));

  EVP_CIPHER *fallback =
      EVP_CIPHER_fetch(libctx.get(), AWSLC_TEST_UNBACKED_CIPHER, nullptr);
  ASSERT_NE(nullptr, fallback) << "a declined cipher did not fall through";
  EXPECT_STREQ(
      "default",
      OSSL_PROVIDER_get0_name(EVP_CIPHER_get0_provider(fallback)));
  EVP_CIPHER_free(fallback);
}

}  // namespace
}  // namespace awslc_provider_test
