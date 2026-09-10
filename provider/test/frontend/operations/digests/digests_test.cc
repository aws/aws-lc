// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Properties of the digest operation class.
//
// These hold for every digest the provider registers rather than for one
// algorithm, so they live here rather than in a per-algorithm file: adding a
// variant should not add another copy of them. Each is driven through SHA-256 as
// the representative, and each is about how our slots handle OSSL_PARAM rather
// than about any transform.

#include "test/test_fixture.h"

#include <openssl/core_names.h>
#include <openssl/evp.h>
#include <openssl/params.h>

namespace awslc_provider_test {
namespace {

// The representative. Which algorithm this is does not matter to these
// assertions, only that it is one we serve.
constexpr const char *kRepresentative = "SHA2-256";

// The init slot's trailing array is NOT digest-scoped: OpenSSL threads the
// caller's whole signature parameter set through it, so keys like "pad-mode"
// arrive there from EVP_DigestSignInit_ex. A provider that rejects unrecognized
// keys in this slot breaks correct callers.
//
// Without this test the failure is invisible from the digest suite: it surfaces
// only when someone signs with parameters, and then it looks like a signature bug.
TEST_F(ProviderTest, DigestInitIgnoresForeignParams) {
  MdPtr md(EVP_MD_fetch(libctx(), kRepresentative, kRequireAwslc));
  ASSERT_TRUE(md);

  MdCtxPtr ctx(EVP_MD_CTX_new());
  ASSERT_TRUE(ctx);

  int saltlen = 20;
  OSSL_PARAM params[] = {
      OSSL_PARAM_construct_utf8_string(OSSL_SIGNATURE_PARAM_PAD_MODE,
                                       const_cast<char *>("pss"), 0),
      OSSL_PARAM_construct_int(OSSL_SIGNATURE_PARAM_PSS_SALTLEN, &saltlen),
      OSSL_PARAM_construct_end()};

  EXPECT_TRUE(EVP_DigestInit_ex2(ctx.get(), md.get(), params))
      << "init rejected foreign params, which breaks EVP_DigestSignInit_ex";
}

// The digest-scoped array, where rejecting an unhandled key is the correct
// behavior: we register no set_ctx_params slot, so setting one must fail rather
// than be silently dropped. This also covers the XOF-length request a non-XOF
// digest must refuse.
TEST_F(ProviderTest, DigestRejectsUnknownCtxParams) {
  MdPtr md(EVP_MD_fetch(libctx(), kRepresentative, kRequireAwslc));
  ASSERT_TRUE(md);

  MdCtxPtr ctx(EVP_MD_CTX_new());
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(EVP_DigestInit_ex(ctx.get(), md.get(), nullptr));

  size_t xoflen = 16;
  OSSL_PARAM params[] = {
      OSSL_PARAM_construct_size_t(OSSL_DIGEST_PARAM_XOFLEN, &xoflen),
      OSSL_PARAM_construct_end()};

  EXPECT_FALSE(EVP_MD_CTX_set_params(ctx.get(), params))
      << "provider accepted a parameter it does not implement";
}

}  // namespace
}  // namespace awslc_provider_test
