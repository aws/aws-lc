// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "test/test_fixture.h"

#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/core_dispatch.h>
#include <openssl/core_names.h>
#include <openssl/evp.h>
#include <openssl/indicator.h>
#include <openssl/param_build.h>
#include <openssl/params.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>

#include <algorithm>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <iterator>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

#include "internal/backend.h"

namespace awslc_provider_test {
namespace {

#ifndef AWSLC_PROVIDER_CONFIG_FILE
#error "AWSLC_PROVIDER_CONFIG_FILE must be defined by the build"
#endif

#if defined(AWSLC_FIPS)
constexpr int kFipsBuild = 1;
#else
constexpr int kFipsBuild = 0;
#endif

// openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048
constexpr char kRsa2048Pem[] = R"(-----BEGIN PRIVATE KEY-----
MIIEvAIBADANBgkqhkiG9w0BAQEFAASCBKYwggSiAgEAAoIBAQDeKYEu72PGoR5r
13nd4eJ/fwxCXD9PjeDiWNCwxOHI3XfIYEs7xccWagwbANbqJANdOFSYOOAcVkPP
OC+p8htNSwKnK3qkobLttwVfCM+WxfeV/id62BlJdSqLfYWe8cmmo2P8CkvKzyTG
59p1qWyNJeQ5zf8RGfGG+TCbuVQO2f+WbC5JFywXbyQLx8VS7vdFXG1od1/ue3sl
FyCI7tZpEZPnpPioWbPT9JKLwLO31wLLhrcnUUUZqHRmkn/M3YcUghuJllqEZz1g
FdVJa4dj/neQaGQcT6Ht+EQFVBH7v9rRQ2JV/n2axr/rjy42XZ8hfCn7Fip97Il4
FHdyVO2RAgMBAAECggEAKuUFIBiRIXoc61IOoeh6CMdxSMPSZowckl93JdZRyOx3
8vyisg8JFlsR7MnP9SPQcXiNntmGbfo6/ADbdRr9qgIUaE4VD0H4T/0hQJztJe2h
1PheS5H7aetBNG8fNFX3ayELjk+3nBg8P9pm3AaDIsqg4wdS2wyxDXBCMiMJp5cU
MlkStLqMjutIU6zt8+/DqSXCK0uHS/rbP3BC0a9MzrixgEq7nDEKEQp25MBXoB+t
0JbEeIl9qPhDh6kkaUub8xQT3ap8NHnSL+rE9VWyDVlpq7u4vG9sz4joEQVYHjmW
3zbpx9BgrGXwQDOv82C257Toqvb5qhYM0onm5JKQhQKBgQDupWUtoS7cGJMfH1oH
UL2PjNbryEkMDoMFdPddby2YacbXEf/1KxdyUOgNCB5yfWBdWj3yS04TELN7XoSf
v6ROhn4mQV5eorq0hD0y8kaafV/S00WjA80L8QNjJSHKJB45xw6q2xAS8Ur47pwf
K8ARhsfG8w6y2OsJfdgN8NNWxQKBgQDuUT8P36yveiVyw7AkscuHebH+Sfy4DzUK
2Kl9mPnf2Jb4HLTz5IFoRKPlvo/5L5faFWhoyAEwRpKMV1JKW4cdtEbvO62qhdGl
NoXtOAfZtzvmXuvjVCiNYWzWRq8nll8fSpNg3v8Y9T82WkrNogB5BAGq1t/q+yvL
hNHmyvtIXQKBgG2r6NGNb2GKkaIN4GvYOSVNTj/RLXCzApdxZ3Sy8TtH8S9JgF2F
TiMk9191ybhH0g9Ut38wCFNOq40YpM5dXf8QY8zk4Z+QHUl0NEPDf5rj3zOeEDSY
PJUuT6YynFKvQoy+5Ai037A034WC8pCIpJ3pWMofTTP36BvWj4HomNcZAoGARf42
t0LKRP9q4Dn5Ec3mKPPlAvpX7vcIbRcVMH4tZUEHlfdYbgk+uJDwUhmVz2na/4Iq
GBwlvTf88pry4EPheyfnbXvplZuX5x4MV4+NPrRCM3bNcQbWoi9q98PqzYWsilQs
1NaptXrSBfSe46Yg3Wn/010ohqseQbfQrigPhUECgYAQdaY6kGueFlQHU8T+FTsL
tfu2IVJg67HOn0fTVjLxDxwG8R1BgnU56FBBNS31HyKW0Dh45A+2ZWH/Bo23vePm
xiWjXvH6nxGHNwBJW1RPFTUyWIvyNrCI+gbpdRKfZQBOPg/+z0/c1xUmmYNrhu5G
j0No0XJrRPSZpi/nsuYVHQ==
-----END PRIVATE KEY-----
)";

constexpr char kMessage[] = "RSA key management";

// How the provider tags AWS-LC's RSA reasons. The backend suite pins these
// values against AWS-LC's headers.
constexpr int kAwslcLibRsa = 4;
constexpr int kAwslcRsaBadRsaParameters = 104;
constexpr int kAwslcRsaNNotEqualPQ = 132;

constexpr const char *kRequireDefault = "provider=default";

// Every component name OpenSSL uses for a two-prime key, in export order.
constexpr const char *kComponents[] = {
    OSSL_PKEY_PARAM_RSA_N,         OSSL_PKEY_PARAM_RSA_E,
    OSSL_PKEY_PARAM_RSA_D,         OSSL_PKEY_PARAM_RSA_FACTOR1,
    OSSL_PKEY_PARAM_RSA_FACTOR2,   OSSL_PKEY_PARAM_RSA_EXPONENT1,
    OSSL_PKEY_PARAM_RSA_EXPONENT2, OSSL_PKEY_PARAM_RSA_COEFFICIENT1};

struct PkeyDeleter {
  void operator()(EVP_PKEY *pkey) const { EVP_PKEY_free(pkey); }
};
struct PkeyCtxDeleter {
  void operator()(EVP_PKEY_CTX *ctx) const { EVP_PKEY_CTX_free(ctx); }
};
struct KeymgmtDeleter {
  void operator()(EVP_KEYMGMT *keymgmt) const { EVP_KEYMGMT_free(keymgmt); }
};
struct ParamsDeleter {
  void operator()(OSSL_PARAM *params) const { OSSL_PARAM_free(params); }
};
struct ParamBldDeleter {
  void operator()(OSSL_PARAM_BLD *bld) const { OSSL_PARAM_BLD_free(bld); }
};
struct BnDeleter {
  void operator()(BIGNUM *bn) const { BN_free(bn); }
};
struct BioDeleter {
  void operator()(BIO *bio) const { BIO_free(bio); }
};

using PkeyPtr = std::unique_ptr<EVP_PKEY, PkeyDeleter>;
using PkeyCtxPtr = std::unique_ptr<EVP_PKEY_CTX, PkeyCtxDeleter>;
using KeymgmtPtr = std::unique_ptr<EVP_KEYMGMT, KeymgmtDeleter>;
using ParamsPtr = std::unique_ptr<OSSL_PARAM, ParamsDeleter>;
using ParamBldPtr = std::unique_ptr<OSSL_PARAM_BLD, ParamBldDeleter>;
using BnPtr = std::unique_ptr<BIGNUM, BnDeleter>;
using BioPtr = std::unique_ptr<BIO, BioDeleter>;

// Exported components by name, as hex.
using Components = std::map<std::string, std::string>;

std::string Hex(const BIGNUM *bn) {
  char *hex = BN_bn2hex(bn);
  std::string out = hex == nullptr ? "<unprintable>" : hex;
  OPENSSL_free(hex);
  return out;
}

Components ComponentsOf(const OSSL_PARAM *params) {
  Components out;
  for (const OSSL_PARAM *p = params; p != nullptr && p->key != nullptr; p++) {
    BIGNUM *bn = nullptr;
    out[p->key] = OSSL_PARAM_get_BN(p, &bn) ? Hex(bn) : "<not an integer>";
    BN_free(bn);
  }
  return out;
}

Components Exported(const EVP_PKEY *pkey, int selection = EVP_PKEY_KEYPAIR) {
  OSSL_PARAM *params = nullptr;
  if (!EVP_PKEY_todata(pkey, selection, &params)) {
    return {{"<export failed>", ""}};
  }
  Components out = ComponentsOf(params);
  OSSL_PARAM_free(params);
  return out;
}

std::set<std::string> Names(const OSSL_PARAM *params) {
  std::set<std::string> names;
  for (const OSSL_PARAM *p = params; p != nullptr && p->key != nullptr; p++) {
    names.insert(p->key);
  }
  return names;
}

std::string ProviderOf(const EVP_PKEY *pkey) {
  const OSSL_PROVIDER *provider = EVP_PKEY_get0_provider(pkey);
  return provider == nullptr ? "<none>" : OSSL_PROVIDER_get0_name(provider);
}

BnPtr GetBn(const EVP_PKEY *pkey, const char *name) {
  BIGNUM *bn = nullptr;
  return BnPtr(EVP_PKEY_get_bn_param(pkey, name, &bn) ? bn : nullptr);
}

// The params for |bns|, built the way an application would.
ParamsPtr BuildParams(
    const std::vector<std::pair<const char *, const BIGNUM *>> &bns) {
  ParamBldPtr bld(OSSL_PARAM_BLD_new());
  if (!bld) {
    return nullptr;
  }
  for (const auto &bn : bns) {
    if (!OSSL_PARAM_BLD_push_BN(bld.get(), bn.first, bn.second)) {
      return nullptr;
    }
  }
  return ParamsPtr(OSSL_PARAM_BLD_to_param(bld.get()));
}

class RsaKeymgmtTest : public ProviderTest {
 protected:
  // Decode using the default decoder
  PkeyPtr Decode(const char *propq = kRequireDefault) {
    BioPtr bio(BIO_new_mem_buf(kRsa2048Pem, -1));
    if (!bio) {
      return nullptr;
    }
    return PkeyPtr(PEM_read_bio_PrivateKey_ex(bio.get(), nullptr, nullptr,
                                              nullptr, libctx(), propq));
  }

  PkeyPtr FromData(const char *propq, int selection, const OSSL_PARAM *params) {
    PkeyCtxPtr ctx(EVP_PKEY_CTX_new_from_name(libctx(), "RSA", propq));
    EVP_PKEY *pkey = nullptr;
    if (!ctx || EVP_PKEY_fromdata_init(ctx.get()) <= 0 ||
        EVP_PKEY_fromdata(ctx.get(), &pkey, selection,
                          const_cast<OSSL_PARAM *>(params)) <= 0) {
      return nullptr;
    }
    return PkeyPtr(pkey);
  }

  // |src|'s components less |omit|, plus rsa-derive-from-pq when
  // |derive_from_pq| is not negative.
  ParamsPtr ComponentParams(const EVP_PKEY *src,
                            const std::vector<std::string> &omit,
                            int derive_from_pq = -1) {
    ParamBldPtr bld(OSSL_PARAM_BLD_new());
    std::vector<BnPtr> values;
    if (!bld) {
      return nullptr;
    }
    for (const char *name : kComponents) {
      if (std::find(omit.begin(), omit.end(), name) != omit.end()) {
        continue;
      }
      values.push_back(GetBn(src, name));
      if (!values.back() ||
          !OSSL_PARAM_BLD_push_BN(bld.get(), name, values.back().get())) {
        return nullptr;
      }
    }
    if (derive_from_pq >= 0 &&
        !OSSL_PARAM_BLD_push_int(bld.get(), OSSL_PKEY_PARAM_RSA_DERIVE_FROM_PQ,
                                 derive_from_pq)) {
      return nullptr;
    }
    return ParamsPtr(OSSL_PARAM_BLD_to_param(bld.get()));
  }

  // |src|'s components, imported into the key manager |propq| selects.
  PkeyPtr CopyInto(const EVP_PKEY *src, const char *propq,
                   int selection = EVP_PKEY_KEYPAIR) {
    OSSL_PARAM *params = nullptr;
    if (!EVP_PKEY_todata(src, selection, &params)) {
      return nullptr;
    }
    PkeyPtr out = FromData(propq, selection, params);
    OSSL_PARAM_free(params);
    return out;
  }

  PkeyCtxPtr KeygenCtx(const char *propq, int bits, BN_ULONG e = RSA_F4,
                       int primes = 2) {
    PkeyCtxPtr ctx(EVP_PKEY_CTX_new_from_name(libctx(), "RSA", propq));
    BnPtr exponent(BN_new());
    if (!ctx || !exponent || !BN_set_word(exponent.get(), e) ||
        EVP_PKEY_keygen_init(ctx.get()) <= 0 ||
        EVP_PKEY_CTX_set_rsa_keygen_bits(ctx.get(), bits) <= 0 ||
        EVP_PKEY_CTX_set1_rsa_keygen_pubexp(ctx.get(), exponent.get()) <= 0 ||
        EVP_PKEY_CTX_set_rsa_keygen_primes(ctx.get(), primes) <= 0) {
      return nullptr;
    }
    return ctx;
  }

  PkeyPtr Generate(const char *propq, int bits, BN_ULONG e = RSA_F4,
                   int primes = 2) {
    PkeyCtxPtr ctx = KeygenCtx(propq, bits, e, primes);
    EVP_PKEY *pkey = nullptr;
    if (!ctx || EVP_PKEY_generate(ctx.get(), &pkey) <= 0) {
      return nullptr;
    }
    return PkeyPtr(pkey);
  }

  // RSASSA-PKCS1-v1_5 with SHA-256, which is deterministic, so equal keys sign
  // identically. |propq| picks the signer; a key it does not own is exported
  // to it.
  std::vector<unsigned char> Sign(EVP_PKEY *pkey,
                                  const char *propq = kPreferAwslc,
                                  std::string *signer = nullptr) {
    MdCtxPtr ctx(EVP_MD_CTX_new());
    EVP_PKEY_CTX *pctx = nullptr;
    size_t len = 0;

    if (!ctx || !EVP_DigestSignInit_ex(ctx.get(), &pctx, "SHA2-256", libctx(),
                                       propq, pkey, nullptr)) {
      return {};
    }
    if (signer != nullptr) {
      *signer = OSSL_PROVIDER_get0_name(EVP_PKEY_CTX_get0_provider(pctx));
    }
    if (!EVP_DigestSign(ctx.get(), nullptr, &len,
                        reinterpret_cast<const unsigned char *>(kMessage),
                        sizeof(kMessage) - 1)) {
      return {};
    }
    std::vector<unsigned char> sig(len);
    if (!EVP_DigestSign(ctx.get(), sig.data(), &len,
                        reinterpret_cast<const unsigned char *>(kMessage),
                        sizeof(kMessage) - 1)) {
      return {};
    }
    sig.resize(len);
    return sig;
  }

  bool Verify(EVP_PKEY *pkey, const std::vector<unsigned char> &sig,
              const char *propq = kPreferAwslc) {
    MdCtxPtr ctx(EVP_MD_CTX_new());
    return ctx &&
           EVP_DigestVerifyInit_ex(ctx.get(), nullptr, "SHA2-256", libctx(),
                                   propq, pkey, nullptr) == 1 &&
           EVP_DigestVerify(ctx.get(), sig.data(), sig.size(),
                            reinterpret_cast<const unsigned char *>(kMessage),
                            sizeof(kMessage) - 1) == 1;
  }
};

TEST_F(RsaKeymgmtTest, ResolvesUnderEveryAdvertisedName) {
  for (const char *name : {"RSA", "rsaEncryption", "1.2.840.113549.1.1.1"}) {
    KeymgmtPtr keymgmt(EVP_KEYMGMT_fetch(libctx(), name, kRequireAwslc));
    ASSERT_TRUE(keymgmt) << "advertised name '" << name << "' did not resolve";
    EXPECT_STREQ(kProviderName, OSSL_PROVIDER_get0_name(
                                    EVP_KEYMGMT_get0_provider(keymgmt.get())));
  }
}

TEST_F(RsaKeymgmtTest, GeneratesAwslcKey) {
  PkeyPtr key = Generate(kRequireAwslc, 2048);
  ASSERT_TRUE(key);
  EXPECT_EQ(kProviderName, ProviderOf(key.get()));
  EXPECT_EQ(2048, EVP_PKEY_get_bits(key.get()));
  EXPECT_EQ(256, EVP_PKEY_get_size(key.get()));
  EXPECT_EQ(112, EVP_PKEY_get_security_bits(key.get()));
  EXPECT_EQ(0ul, ERR_peek_error())
      << "a successful keygen left the queue dirty";
}

TEST_F(RsaKeymgmtTest, GeneratedKeyIsUsableByDefault) {
  // Generate key with LC
  PkeyPtr key = Generate(kRequireAwslc, 2048);
  ASSERT_TRUE(key);
  ASSERT_EQ(kProviderName, ProviderOf(key.get()));

  // Sign with default
  std::string signer;
  const std::vector<unsigned char> sig =
      Sign(key.get(), kRequireDefault, &signer);
  ASSERT_FALSE(sig.empty());
  EXPECT_EQ("default", signer);

  // Encode with default
  BioPtr pkcs8(BIO_new(BIO_s_mem()));
  BioPtr spki(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(pkcs8);
  ASSERT_TRUE(spki);
  ASSERT_TRUE(PEM_write_bio_PrivateKey_ex(pkcs8.get(), key.get(), nullptr,
                                          nullptr, 0, nullptr, nullptr,
                                          libctx(), kRequireDefault));
  ASSERT_TRUE(PEM_write_bio_PUBKEY_ex(spki.get(), key.get(), libctx(),
                                      kRequireDefault));

  // Decode with default
  PkeyPtr priv(PEM_read_bio_PrivateKey_ex(pkcs8.get(), nullptr, nullptr,
                                          nullptr, libctx(), kRequireDefault));
  PkeyPtr pub(PEM_read_bio_PUBKEY_ex(spki.get(), nullptr, nullptr, nullptr,
                                     libctx(), kRequireDefault));
  ASSERT_TRUE(priv);
  ASSERT_TRUE(pub);
  // Verify with default
  for (EVP_PKEY *decoded : {priv.get(), pub.get()}) {
    EXPECT_EQ("default", ProviderOf(decoded));
    EXPECT_TRUE(Verify(decoded, sig, kRequireDefault));
    EXPECT_EQ(1, EVP_PKEY_eq(decoded, key.get()));
    EXPECT_EQ(1, EVP_PKEY_eq(key.get(), decoded));
  }
  EXPECT_EQ(Exported(key.get()), Exported(priv.get()));
}

// default -> awslc -> default.
TEST_F(RsaKeymgmtTest, ImportsDecodedKeyAndRoundTrips) {
  // Decode PEM with default
  PkeyPtr decoded = Decode();
  ASSERT_TRUE(decoded);
  EXPECT_EQ("default", ProviderOf(decoded.get()));

  // Import into LC
  PkeyPtr imported = CopyInto(decoded.get(), kRequireAwslc);
  ASSERT_TRUE(imported);
  EXPECT_EQ(kProviderName, ProviderOf(imported.get()));

  // Sign
  const std::vector<unsigned char> expected =
      Sign(decoded.get(), kRequireDefault);
  ASSERT_FALSE(expected.empty());
  EXPECT_EQ(expected, Sign(imported.get(), kRequireDefault));

  // Import into default and compare
  PkeyPtr returned = CopyInto(imported.get(), kRequireDefault);
  ASSERT_TRUE(returned);
  EXPECT_EQ("default", ProviderOf(returned.get()));
  EXPECT_EQ(Exported(decoded.get()), Exported(returned.get()));
}

// EVP_PKEY_eq with a default key first imports that key into us and asks our
// match. Were the import to fail, libcrypto would quietly retry in the other
// direction with default's match, so the clean queue is the witness that it
// did not.
TEST_F(RsaKeymgmtTest, ImplicitBridgeImportsAndMatches) {
  PkeyPtr decoded = Decode();
  ASSERT_TRUE(decoded);
  PkeyPtr imported = CopyInto(decoded.get(), kRequireAwslc);
  ASSERT_TRUE(imported);

  ERR_clear_error();
  EXPECT_EQ(1, EVP_PKEY_eq(decoded.get(), imported.get()));
  EXPECT_EQ(0ul, ERR_peek_error());

  BnPtr n = GetBn(decoded.get(), OSSL_PKEY_PARAM_RSA_N);
  BnPtr e = GetBn(decoded.get(), OSSL_PKEY_PARAM_RSA_E);
  ASSERT_TRUE(n);
  ASSERT_TRUE(e);
  ASSERT_TRUE(BN_add_word(n.get(), 2));
  ParamsPtr params = BuildParams(
      {{OSSL_PKEY_PARAM_RSA_N, n.get()}, {OSSL_PKEY_PARAM_RSA_E, e.get()}});
  ASSERT_TRUE(params);
  PkeyPtr other = FromData(kRequireDefault, EVP_PKEY_PUBLIC_KEY, params.get());
  ASSERT_TRUE(other);

  EXPECT_EQ(0, EVP_PKEY_eq(other.get(), imported.get()));
  EXPECT_EQ(0ul, ERR_peek_error());
}

TEST_F(RsaKeymgmtTest, ImportsEverySupportedShape) {
  PkeyPtr decoded = Decode();
  ASSERT_TRUE(decoded);

  {
    SCOPED_TRACE("full key");
    PkeyPtr ours = CopyInto(decoded.get(), kRequireAwslc);
    ASSERT_TRUE(ours);
    EXPECT_EQ(Exported(decoded.get()), Exported(ours.get()));
  }
  {
    SCOPED_TRACE("n, e, d only");
    ParamsPtr params = ComponentParams(
        decoded.get(),
        {OSSL_PKEY_PARAM_RSA_FACTOR1, OSSL_PKEY_PARAM_RSA_FACTOR2,
         OSSL_PKEY_PARAM_RSA_EXPONENT1, OSSL_PKEY_PARAM_RSA_EXPONENT2,
         OSSL_PKEY_PARAM_RSA_COEFFICIENT1});
    ASSERT_TRUE(params);
    PkeyPtr ours = FromData(kRequireAwslc, EVP_PKEY_KEYPAIR, params.get());
    PkeyPtr theirs = FromData(kRequireDefault, EVP_PKEY_KEYPAIR, params.get());
    ASSERT_TRUE(ours);
    ASSERT_TRUE(theirs);
    EXPECT_EQ(kProviderName, ProviderOf(ours.get()));
    EXPECT_EQ(Exported(theirs.get()), Exported(ours.get()));
    EXPECT_EQ(Sign(theirs.get()), Sign(ours.get()));
  }
  {
    SCOPED_TRACE("unknown keys alongside every component");
    // The builder reads each BIGNUM only at OSSL_PARAM_BLD_to_param.
    ParamBldPtr bld(OSSL_PARAM_BLD_new());
    std::vector<BnPtr> values;
    ASSERT_TRUE(bld);
    for (const char *name : kComponents) {
      values.push_back(GetBn(decoded.get(), name));
      ASSERT_TRUE(values.back());
      ASSERT_TRUE(OSSL_PARAM_BLD_push_BN(bld.get(), name, values.back().get()));
    }
    ASSERT_TRUE(OSSL_PARAM_BLD_push_int(bld.get(), "not-an-rsa-key", 1));
    ParamsPtr params(OSSL_PARAM_BLD_to_param(bld.get()));
    ASSERT_TRUE(params);
    PkeyPtr ours = FromData(kRequireAwslc, EVP_PKEY_KEYPAIR, params.get());
    ASSERT_TRUE(ours);
    EXPECT_EQ(Exported(decoded.get()), Exported(ours.get()));
  }
  {
    SCOPED_TRACE("public only");
    PkeyPtr ours = CopyInto(decoded.get(), kRequireAwslc, EVP_PKEY_PUBLIC_KEY);
    ASSERT_TRUE(ours);
    const Components components = Exported(ours.get());
    EXPECT_EQ(
        (std::set<std::string>{OSSL_PKEY_PARAM_RSA_N, OSSL_PKEY_PARAM_RSA_E}),
        [&] {
          std::set<std::string> names;
          for (const auto &c : components) {
            names.insert(c.first);
          }
          return names;
        }());
    EXPECT_EQ(1, EVP_PKEY_eq(ours.get(), decoded.get()));
  }
  {
    SCOPED_TRACE("e over 33 bits, generated by default");
    PkeyPtr large =
        Generate(kRequireDefault, 2048, (static_cast<BN_ULONG>(1) << 34) + 1);
    ASSERT_TRUE(large);
    PkeyPtr ours = CopyInto(large.get(), kRequireAwslc);
    ASSERT_TRUE(ours);
    EXPECT_EQ(Exported(large.get()), Exported(ours.get()));
    EXPECT_EQ(Sign(large.get()), Sign(ours.get()));
  }
}

TEST_F(RsaKeymgmtTest, RefusesShapesAwslcCannotRepresent) {
  PkeyPtr decoded = Decode();
  ASSERT_TRUE(decoded);

  struct Case {
    const char *label;
    std::vector<std::string> omit;
    int derive_from_pq;
    const char *refused;
  };
  const Case cases[] = {
      {"partial CRT set",
       {OSSL_PKEY_PARAM_RSA_COEFFICIENT1},
       -1,
       "RSA"},
      {"factors without CRT values",
       {OSSL_PKEY_PARAM_RSA_EXPONENT1, OSSL_PKEY_PARAM_RSA_EXPONENT2,
        OSSL_PKEY_PARAM_RSA_COEFFICIENT1},
       -1,
       "RSA"},
      {"derive-from-pq",
       {OSSL_PKEY_PARAM_RSA_EXPONENT1, OSSL_PKEY_PARAM_RSA_EXPONENT2,
        OSSL_PKEY_PARAM_RSA_COEFFICIENT1},
       1,
       OSSL_PKEY_PARAM_RSA_DERIVE_FROM_PQ},
  };
  for (const Case &c : cases) {
    SCOPED_TRACE(c.label);
    ParamsPtr params = ComponentParams(decoded.get(), c.omit, c.derive_from_pq);
    ASSERT_TRUE(params);

    ERR_clear_error();
    EXPECT_FALSE(FromData(kRequireAwslc, EVP_PKEY_KEYPAIR, params.get()));
    const std::vector<ErrorRecord> ours = ProviderErrors(DrainErrors());
    ASSERT_EQ(1u, ours.size());
    EXPECT_EQ((unsigned long)AWSLC_PROV_R_INVALID_PARAMETER, ours[0].reason());
    EXPECT_EQ(c.refused, ours[0].data);
  }

  {
    SCOPED_TRACE("three primes, generated by default");
    PkeyPtr multi = Generate(kRequireDefault, 2048, RSA_F4, 3);
    ASSERT_TRUE(multi);
    ASSERT_EQ(1u, Exported(multi.get()).count(OSSL_PKEY_PARAM_RSA_FACTOR3));

    ERR_clear_error();
    EXPECT_FALSE(CopyInto(multi.get(), kRequireAwslc));
    const std::vector<ErrorRecord> ours = ProviderErrors(DrainErrors());
    ASSERT_EQ(1u, ours.size());
    EXPECT_EQ((unsigned long)AWSLC_PROV_R_INVALID_PARAMETER, ours[0].reason());
    EXPECT_EQ(OSSL_PKEY_PARAM_RSA_FACTOR3, ours[0].data);
  }
}

// AWS-LC, not the provider, rejects this key, and the record says so.
TEST_F(RsaKeymgmtTest, ReportsAwslcOriginImportFailure) {
  PkeyPtr decoded = Decode();
  ASSERT_TRUE(decoded);
  OSSL_PARAM *exported = nullptr;
  ASSERT_TRUE(EVP_PKEY_todata(decoded.get(), EVP_PKEY_KEYPAIR, &exported));
  ParamsPtr params(exported);

  OSSL_PARAM *q = OSSL_PARAM_locate(params.get(), OSSL_PKEY_PARAM_RSA_FACTOR2);
  ASSERT_NE(nullptr, q);
  BIGNUM *raw_q = nullptr;
  ASSERT_TRUE(OSSL_PARAM_get_BN(q, &raw_q));
  BnPtr wrong_q(raw_q);
  ASSERT_TRUE(BN_add_word(wrong_q.get(), 2));
  ASSERT_TRUE(OSSL_PARAM_set_BN(q, wrong_q.get()));

  ERR_clear_error();
  EXPECT_FALSE(FromData(kRequireAwslc, EVP_PKEY_KEYPAIR, params.get()));
  const std::vector<ErrorRecord> all = DrainErrors();
  const std::vector<ErrorRecord> ours = ProviderErrors(all);
  ASSERT_EQ(1u, ours.size());
  EXPECT_EQ((unsigned long)AWSLC_PROV_ERROR_REASON(kAwslcLibRsa,
                                                   kAwslcRsaNNotEqualPQ),
            ours[0].reason());
  EXPECT_NE(std::string::npos, ours[0].data.find("AWS-LC")) << ours[0].data;
  EXPECT_NE(std::string::npos, ours[0].data.find("N_NOT_EQUAL_P_Q"))
      << ours[0].data;
  for (const ErrorRecord &record : all) {
    EXPECT_FALSE(record.library() == (unsigned long)kAwslcLibRsa &&
                 record.reason() == (unsigned long)kAwslcRsaNNotEqualPQ)
        << "AWS-LC's library id reached OpenSSL's queue untranslated";
  }
}

TEST_F(RsaKeymgmtTest, DeclaresExactParamLists) {
  KeymgmtPtr ours(EVP_KEYMGMT_fetch(libctx(), "RSA", kRequireAwslc));
  KeymgmtPtr theirs(EVP_KEYMGMT_fetch(libctx(), "RSA", kRequireDefault));
  ASSERT_TRUE(ours);
  ASSERT_TRUE(theirs);

  std::map<std::string, unsigned> ours_settable;
  std::map<std::string, unsigned> theirs_settable;
  for (const OSSL_PARAM *p = EVP_KEYMGMT_gen_settable_params(ours.get());
       p != nullptr && p->key != nullptr; p++) {
    ours_settable[p->key] = p->data_type;
  }
  for (const OSSL_PARAM *p = EVP_KEYMGMT_gen_settable_params(theirs.get());
       p != nullptr && p->key != nullptr; p++) {
    theirs_settable[p->key] = p->data_type;
  }
  EXPECT_EQ(theirs_settable, ours_settable);

  EXPECT_EQ(std::set<std::string>{OSSL_PKEY_PARAM_FIPS_APPROVED_INDICATOR},
            Names(EVP_KEYMGMT_gen_gettable_params(ours.get())));

  std::set<std::string> gettable = {
      OSSL_PKEY_PARAM_BITS, OSSL_PKEY_PARAM_SECURITY_BITS,
      OSSL_PKEY_PARAM_MAX_SIZE, OSSL_PKEY_PARAM_DEFAULT_DIGEST};
  gettable.insert(std::begin(kComponents), std::end(kComponents));
  EXPECT_EQ(gettable, Names(EVP_KEYMGMT_gettable_params(ours.get())));
}

TEST_F(RsaKeymgmtTest, RefusesUnsupportedGenParams) {
  PkeyCtxPtr ctx(EVP_PKEY_CTX_new_from_name(libctx(), "RSA", kRequireAwslc));
  ASSERT_TRUE(ctx);
  ASSERT_GT(EVP_PKEY_keygen_init(ctx.get()), 0);

  ERR_clear_error();
  // AWS-LC bounds the size at generate; only a value past unsigned is refused.
  for (int bits : {128, 3000, 16384 + 128}) {
    SCOPED_TRACE(bits);
    EXPECT_GT(EVP_PKEY_CTX_set_rsa_keygen_bits(ctx.get(), bits), 0);
  }
  EXPECT_EQ(0ul, ERR_peek_error());
  if (sizeof(size_t) > sizeof(unsigned)) {
    size_t wide = (size_t)UINT_MAX + 1 + 2048;
    OSSL_PARAM too_wide[] = {
        OSSL_PARAM_construct_size_t(OSSL_PKEY_PARAM_RSA_BITS, &wide),
        OSSL_PARAM_construct_end()};
    EXPECT_FALSE(EVP_PKEY_CTX_set_params(ctx.get(), too_wide));
    std::vector<ErrorRecord> ours = ProviderErrors(DrainErrors());
    ASSERT_EQ(1u, ours.size());
    EXPECT_EQ((unsigned long)AWSLC_PROV_R_INVALID_PARAMETER, ours[0].reason());
    EXPECT_EQ(OSSL_PKEY_PARAM_RSA_BITS, ours[0].data);
  }

  EXPECT_LE(EVP_PKEY_CTX_set_rsa_keygen_primes(ctx.get(), 3), 0);
  std::vector<ErrorRecord> ours = ProviderErrors(DrainErrors());
  ASSERT_EQ(1u, ours.size());
  EXPECT_EQ(OSSL_PKEY_PARAM_RSA_PRIMES, ours[0].data);

  int unknown = 1;
  OSSL_PARAM foreign[] = {OSSL_PARAM_construct_int("not-an-rsa-key", &unknown),
                          OSSL_PARAM_construct_end()};
  EXPECT_TRUE(EVP_PKEY_CTX_set_params(ctx.get(), foreign));

  // The legacy control strings resolve through the settable list.
  EXPECT_GT(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_keygen_bits", "2048"), 0);
  EXPECT_GT(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_keygen_bits", "1000"), 0);
  EXPECT_LE(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_keygen_primes", "3"), 0);
  EXPECT_GT(EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_keygen_pubexp", "65537"), 0);
  ERR_clear_error();
}

TEST_F(RsaKeymgmtTest, RefusesPublicExponentOtherThan65537) {
  PkeyCtxPtr ctx(EVP_PKEY_CTX_new_from_name(libctx(), "RSA", kRequireAwslc));
  ASSERT_TRUE(ctx);
  ASSERT_GT(EVP_PKEY_keygen_init(ctx.get()), 0);
  BnPtr three(BN_new());
  ASSERT_TRUE(three);
  ASSERT_TRUE(BN_set_word(three.get(), 3));

  ERR_clear_error();
  EXPECT_LE(EVP_PKEY_CTX_set1_rsa_keygen_pubexp(ctx.get(), three.get()), 0);
  const std::vector<ErrorRecord> ours = ProviderErrors(DrainErrors());
  ASSERT_EQ(1u, ours.size());
  EXPECT_EQ((unsigned long)AWSLC_PROV_R_INVALID_PARAMETER, ours[0].reason());
  EXPECT_EQ(OSSL_PKEY_PARAM_RSA_E, ours[0].data);

  PkeyPtr key = Generate(kRequireAwslc, 2048, RSA_F4);
  ASSERT_TRUE(key);
  BnPtr e = GetBn(key.get(), OSSL_PKEY_PARAM_RSA_E);
  ASSERT_TRUE(e);
  EXPECT_TRUE(BN_is_word(e.get(), RSA_F4));
}

// Not default's formula, which reports more between rows; TLS levels differ.
TEST_F(RsaKeymgmtTest, ReportsSp80057StrengthAtTableBoundaries) {
  PkeyCtxPtr ctx(EVP_PKEY_CTX_new_from_name(libctx(), "RSA", kRequireAwslc));
  BnPtr e(BN_new());
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(e);
  ASSERT_TRUE(BN_set_word(e.get(), RSA_F4));
  ASSERT_GT(EVP_PKEY_fromdata_init(ctx.get()), 0);

  const struct {
    int modulus_bits;
    int strength;
  } kCases[] = {
      {512, 0},     {1023, 0},    {1024, 80},   {2047, 80},
      {2048, 112},  {3071, 112},  {3072, 128},  {7679, 128},
      {7680, 192},  {15359, 192}, {15360, 256}, {16384, 256},
  };
  for (const auto &c : kCases) {
    SCOPED_TRACE(c.modulus_bits);
    BnPtr n(BN_new());
    ASSERT_TRUE(n);
    ASSERT_TRUE(BN_set_bit(n.get(), c.modulus_bits - 1));
    ASSERT_TRUE(BN_set_bit(n.get(), 0));
    ParamsPtr params = BuildParams(
        {{OSSL_PKEY_PARAM_RSA_N, n.get()}, {OSSL_PKEY_PARAM_RSA_E, e.get()}});
    ASSERT_TRUE(params);
    EVP_PKEY *raw = nullptr;
    ASSERT_GT(
        EVP_PKEY_fromdata(ctx.get(), &raw, EVP_PKEY_PUBLIC_KEY, params.get()),
        0);
    PkeyPtr key(raw);
    EXPECT_EQ(kProviderName, ProviderOf(key.get()));
    EXPECT_EQ(c.modulus_bits, EVP_PKEY_get_bits(key.get()));
    int written = -1;
    ASSERT_TRUE(EVP_PKEY_get_int_param(key.get(), OSSL_PKEY_PARAM_SECURITY_BITS,
                                       &written));
    EXPECT_EQ(c.strength, written);
    EXPECT_EQ(c.strength, EVP_PKEY_get_security_bits(key.get()));
  }
}

TEST_F(RsaKeymgmtTest, AnswersComponentRequestsLikeDefault) {
  PkeyPtr theirs = Decode();
  ASSERT_TRUE(theirs);
  PkeyPtr ours = CopyInto(theirs.get(), kRequireAwslc);
  ASSERT_TRUE(ours);

  char theirs_md[64] = {0};
  char ours_md[64] = {0};
  EXPECT_EQ(
      EVP_PKEY_get_default_digest_name(theirs.get(), theirs_md,
                                       sizeof(theirs_md)),
      EVP_PKEY_get_default_digest_name(ours.get(), ours_md, sizeof(ours_md)));
  EXPECT_STREQ(theirs_md, ours_md);

  for (const char *name : kComponents) {
    SCOPED_TRACE(name);
    BnPtr want = GetBn(theirs.get(), name);
    BnPtr got = GetBn(ours.get(), name);
    ASSERT_TRUE(want);
    ASSERT_TRUE(got);
    EXPECT_EQ(0, BN_cmp(want.get(), got.get()));
  }

  // One component carries the size-probe, short-buffer, and padding contract.
  const char *name = OSSL_PKEY_PARAM_RSA_D;
  for (unsigned type : {OSSL_PARAM_UNSIGNED_INTEGER, OSSL_PARAM_INTEGER}) {
    SCOPED_TRACE(type);
    OSSL_PARAM probe[] = {{name, type, nullptr, 0, OSSL_PARAM_UNMODIFIED},
                          OSSL_PARAM_END};
    OSSL_PARAM theirs_probe[] = {
        {name, type, nullptr, 0, OSSL_PARAM_UNMODIFIED}, OSSL_PARAM_END};
    ASSERT_TRUE(EVP_PKEY_get_params(ours.get(), probe));
    ASSERT_TRUE(EVP_PKEY_get_params(theirs.get(), theirs_probe));
    const size_t required = theirs_probe[0].return_size;
    EXPECT_EQ(required, probe[0].return_size);
    ASSERT_GT(required, 1u);

    std::vector<unsigned char> short_buffer(required - 1);
    OSSL_PARAM undersized[] = {{name, type, short_buffer.data(),
                                short_buffer.size(), OSSL_PARAM_UNMODIFIED},
                               OSSL_PARAM_END};
    EXPECT_FALSE(EVP_PKEY_get_params(ours.get(), undersized));
    EXPECT_EQ(required, undersized[0].return_size);
    ERR_clear_error();

    // Padded past the minimum, which default fills to the whole buffer.
    std::vector<unsigned char> ours_bytes(required + 3, 0xa5);
    std::vector<unsigned char> theirs_bytes(required + 3, 0x5a);
    OSSL_PARAM ours_out[] = {{name, type, ours_bytes.data(),
                              ours_bytes.size(), OSSL_PARAM_UNMODIFIED},
                             OSSL_PARAM_END};
    OSSL_PARAM theirs_out[] = {{name, type, theirs_bytes.data(),
                                theirs_bytes.size(), OSSL_PARAM_UNMODIFIED},
                               OSSL_PARAM_END};
    ASSERT_TRUE(EVP_PKEY_get_params(ours.get(), ours_out));
    ASSERT_TRUE(EVP_PKEY_get_params(theirs.get(), theirs_out));
    EXPECT_EQ(theirs_out[0].return_size, ours_out[0].return_size);
    EXPECT_EQ(theirs_bytes, ours_bytes);
  }

  PkeyPtr pub = CopyInto(theirs.get(), kRequireAwslc, EVP_PKEY_PUBLIC_KEY);
  ASSERT_TRUE(pub);
  EXPECT_FALSE(GetBn(pub.get(), OSSL_PKEY_PARAM_RSA_D));
  ERR_clear_error();
}

TEST_F(RsaKeymgmtTest, ValidatesDuplicatesAndExposesLegacyRsa) {
  PkeyPtr decoded = Decode();
  ASSERT_TRUE(decoded);
  PkeyPtr ours = CopyInto(decoded.get(), kRequireAwslc);
  ASSERT_TRUE(ours);

  PkeyCtxPtr ctx(EVP_PKEY_CTX_new_from_pkey(libctx(), ours.get(), nullptr));
  ASSERT_TRUE(ctx);
  EXPECT_EQ(1, EVP_PKEY_check(ctx.get()));

  PkeyPtr duplicate(EVP_PKEY_dup(ours.get()));
  ASSERT_TRUE(duplicate);
  EXPECT_EQ(kProviderName, ProviderOf(duplicate.get()));
  const std::vector<unsigned char> sig = Sign(ours.get());
  ASSERT_FALSE(sig.empty());
  EXPECT_EQ(sig, Sign(duplicate.get()));

  BnPtr want_n = GetBn(decoded.get(), OSSL_PKEY_PARAM_RSA_N);
  BnPtr want_d = GetBn(decoded.get(), OSSL_PKEY_PARAM_RSA_D);
  ASSERT_TRUE(want_n);
  ASSERT_TRUE(want_d);
#if defined(__GNUC__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#endif
  RSA *legacy = EVP_PKEY_get1_RSA(ours.get());
  ASSERT_NE(nullptr, legacy);
  const BIGNUM *n = nullptr;
  const BIGNUM *d = nullptr;
  RSA_get0_key(legacy, &n, nullptr, &d);
  EXPECT_EQ(0, BN_cmp(want_n.get(), n));
  EXPECT_EQ(0, BN_cmp(want_d.get(), d));
  RSA_free(legacy);
#if defined(__GNUC__)
#pragma GCC diagnostic pop
#endif
}

int g_unapproved_calls = 0;

int CountUnapproved(const char *, const char *, const OSSL_PARAM[]) {
  g_unapproved_calls++;
  return 0;
}

int KeygenIndicator(EVP_PKEY_CTX *ctx) {
  int approved = -1;
  OSSL_PARAM params[] = {
      OSSL_PARAM_construct_int(OSSL_PKEY_PARAM_FIPS_APPROVED_INDICATOR,
                               &approved),
      OSSL_PARAM_construct_end()};
  return EVP_PKEY_CTX_get_params(ctx, params) ? approved : -1;
}

TEST_F(RsaKeymgmtTest, ReportsKeygenFipsIndicator) {
  g_unapproved_calls = 0;
  OSSL_INDICATOR_set_callback(libctx(), CountUnapproved);

  PkeyCtxPtr approved_ctx = KeygenCtx(kRequireAwslc, 2048);
  ASSERT_TRUE(approved_ctx);
  EXPECT_NE(nullptr, OSSL_PARAM_locate_const(
                         EVP_PKEY_CTX_gettable_params(approved_ctx.get()),
                         OSSL_PKEY_PARAM_FIPS_APPROVED_INDICATOR));
  EVP_PKEY *key = nullptr;
  ASSERT_GT(EVP_PKEY_generate(approved_ctx.get(), &key), 0);
  EVP_PKEY_free(key);
  EXPECT_EQ(kFipsBuild, KeygenIndicator(approved_ctx.get()));

  PkeyCtxPtr small_ctx = KeygenCtx(kRequireAwslc, 1024);
  ASSERT_TRUE(small_ctx);
  key = nullptr;
  ERR_clear_error();
  EXPECT_LE(EVP_PKEY_generate(small_ctx.get(), &key), 0);
  EVP_PKEY_free(key);
  const std::vector<ErrorRecord> ours = ProviderErrors(DrainErrors());
  ASSERT_EQ(1u, ours.size());
  EXPECT_EQ((unsigned long)AWSLC_PROV_ERROR_REASON(kAwslcLibRsa,
                                                   kAwslcRsaBadRsaParameters),
            ours[0].reason());
  EXPECT_EQ(0, KeygenIndicator(small_ctx.get()));
  EXPECT_EQ(0, g_unapproved_calls);
  OSSL_INDICATOR_set_callback(libctx(), nullptr);
}

// The slots called the way libcrypto calls them, for selections no public EVP
// path passes.
class RsaKeymgmtSlotsTest : public RsaKeymgmtTest {
 protected:
  void SetUp() override {
    RsaKeymgmtTest::SetUp();
    if (HasFatalFailure()) {
      return;
    }
    int no_cache = 0;
    algorithms_ =
        OSSL_PROVIDER_query_operation(awslc(), OSSL_OP_KEYMGMT, &no_cache);
    for (const OSSL_ALGORITHM *a = algorithms_;
         a != nullptr && a->algorithm_names != nullptr; a++) {
      if (std::string(a->algorithm_names).rfind("RSA:", 0) == 0) {
        functions_ = a->implementation;
      }
    }
    ASSERT_NE(nullptr, functions_);
    provctx_ = OSSL_PROVIDER_get0_provider_ctx(awslc());

    PkeyPtr decoded = Decode();
    ASSERT_TRUE(decoded);
    OSSL_PARAM *params = nullptr;
    ASSERT_TRUE(EVP_PKEY_todata(decoded.get(), EVP_PKEY_KEYPAIR, &params));
    params_.reset(params);
  }

  void TearDown() override {
    OSSL_PROVIDER_unquery_operation(awslc(), OSSL_OP_KEYMGMT, algorithms_);
    RsaKeymgmtTest::TearDown();
  }

  template <typename Fn>
  Fn *Slot(int id) {
    for (const OSSL_DISPATCH *d = functions_; d->function_id != 0; d++) {
      if (d->function_id == id) {
        return reinterpret_cast<Fn *>(d->function);
      }
    }
    return nullptr;
  }

  struct KeyDeleter {
    OSSL_FUNC_keymgmt_free_fn *free_fn;
    void operator()(void *keydata) const { free_fn(keydata); }
  };
  using KeyPtr = std::unique_ptr<void, KeyDeleter>;

  KeyPtr Wrap(void *keydata) {
    return KeyPtr(
        keydata,
        KeyDeleter{Slot<OSSL_FUNC_keymgmt_free_fn>(OSSL_FUNC_KEYMGMT_FREE)});
  }

  KeyPtr Import(int selection) {
    KeyPtr key =
        Wrap(Slot<OSSL_FUNC_keymgmt_new_fn>(OSSL_FUNC_KEYMGMT_NEW)(provctx_));
    if (!key || !Slot<OSSL_FUNC_keymgmt_import_fn>(OSSL_FUNC_KEYMGMT_IMPORT)(
                    key.get(), selection, params_.get())) {
      return Wrap(nullptr);
    }
    return key;
  }

  int Has(const KeyPtr &key, int selection) {
    return Slot<OSSL_FUNC_keymgmt_has_fn>(OSSL_FUNC_KEYMGMT_HAS)(key.get(),
                                                                 selection);
  }

  static int CollectNames(const OSSL_PARAM params[], void *arg) {
    *static_cast<std::set<std::string> *>(arg) = Names(params);
    return 1;
  }

  std::set<std::string> ExportNames(const KeyPtr &key, int selection) {
    std::set<std::string> names = {"<not called>"};
    if (!Slot<OSSL_FUNC_keymgmt_export_fn>(OSSL_FUNC_KEYMGMT_EXPORT)(
            key.get(), selection, CollectNames, &names)) {
      return {"<export failed>"};
    }
    return names;
  }

  const OSSL_ALGORITHM *algorithms_ = nullptr;
  const OSSL_DISPATCH *functions_ = nullptr;
  void *provctx_ = nullptr;
  ParamsPtr params_;
};

TEST_F(RsaKeymgmtSlotsTest, ExportsBySelection) {
  KeyPtr key = Import(OSSL_KEYMGMT_SELECT_KEYPAIR);
  ASSERT_TRUE(key);

  const std::set<std::string> all(std::begin(kComponents),
                                  std::end(kComponents));
  EXPECT_EQ(all, ExportNames(key, OSSL_KEYMGMT_SELECT_KEYPAIR));
  EXPECT_EQ(all, ExportNames(key, OSSL_KEYMGMT_SELECT_PRIVATE_KEY));
  EXPECT_EQ(
      (std::set<std::string>{OSSL_PKEY_PARAM_RSA_N, OSSL_PKEY_PARAM_RSA_E}),
      ExportNames(key, OSSL_KEYMGMT_SELECT_PUBLIC_KEY));
  EXPECT_EQ(std::set<std::string>{},
            ExportNames(key, OSSL_KEYMGMT_SELECT_OTHER_PARAMETERS));

  ERR_clear_error();
  EXPECT_EQ(std::set<std::string>{"<export failed>"},
            ExportNames(key, OSSL_KEYMGMT_SELECT_DOMAIN_PARAMETERS));
  EXPECT_EQ(1u, ProviderErrors(DrainErrors()).size());
}

TEST_F(RsaKeymgmtSlotsTest, MatchesBySelection) {
  auto *match = Slot<OSSL_FUNC_keymgmt_match_fn>(OSSL_FUNC_KEYMGMT_MATCH);
  KeyPtr priv = Import(OSSL_KEYMGMT_SELECT_KEYPAIR);
  KeyPtr pub = Import(OSSL_KEYMGMT_SELECT_PUBLIC_KEY);
  ASSERT_TRUE(priv);
  ASSERT_TRUE(pub);

  EXPECT_TRUE(match(priv.get(), pub.get(), OSSL_KEYMGMT_SELECT_PUBLIC_KEY));
  EXPECT_TRUE(match(priv.get(), pub.get(), OSSL_KEYMGMT_SELECT_KEYPAIR));
  // With only the private key selected, d decides, and the public key has
  // none.
  EXPECT_FALSE(match(priv.get(), pub.get(), OSSL_KEYMGMT_SELECT_PRIVATE_KEY));
  EXPECT_TRUE(match(priv.get(), priv.get(), OSSL_KEYMGMT_SELECT_PRIVATE_KEY));
}

TEST_F(RsaKeymgmtSlotsTest, DuplicatesBySelection) {
  auto *dup = Slot<OSSL_FUNC_keymgmt_dup_fn>(OSSL_FUNC_KEYMGMT_DUP);
  KeyPtr key = Import(OSSL_KEYMGMT_SELECT_KEYPAIR);
  ASSERT_TRUE(key);

  ERR_clear_error();
  EXPECT_FALSE(Wrap(dup(key.get(), OSSL_KEYMGMT_SELECT_ALL_PARAMETERS)));
  EXPECT_EQ(1u, ProviderErrors(DrainErrors()).size());

  KeyPtr pub = Wrap(dup(key.get(), OSSL_KEYMGMT_SELECT_PUBLIC_KEY));
  ASSERT_TRUE(pub);
  EXPECT_TRUE(Has(pub, OSSL_KEYMGMT_SELECT_PUBLIC_KEY));
  EXPECT_FALSE(Has(pub, OSSL_KEYMGMT_SELECT_PRIVATE_KEY));

  KeyPtr priv = Wrap(dup(key.get(), OSSL_KEYMGMT_SELECT_KEYPAIR));
  ASSERT_TRUE(priv);
  EXPECT_TRUE(Has(priv, OSSL_KEYMGMT_SELECT_PRIVATE_KEY));
}

TEST_F(RsaKeymgmtSlotsTest, ValidatesSelectedParts) {
  auto *validate =
      Slot<OSSL_FUNC_keymgmt_validate_fn>(OSSL_FUNC_KEYMGMT_VALIDATE);
  KeyPtr pub = Import(OSSL_KEYMGMT_SELECT_PUBLIC_KEY);
  ASSERT_TRUE(pub);

  EXPECT_TRUE(validate(pub.get(), OSSL_KEYMGMT_SELECT_OTHER_PARAMETERS,
                       OSSL_KEYMGMT_VALIDATE_FULL_CHECK));
  EXPECT_TRUE(validate(pub.get(), OSSL_KEYMGMT_SELECT_PUBLIC_KEY,
                       OSSL_KEYMGMT_VALIDATE_FULL_CHECK));
  ERR_clear_error();
  EXPECT_FALSE(validate(pub.get(), OSSL_KEYMGMT_SELECT_PRIVATE_KEY,
                        OSSL_KEYMGMT_VALIDATE_FULL_CHECK));
  EXPECT_EQ(1u, ProviderErrors(DrainErrors()).size());
}

// The deployed path: provider.cnf installs ?provider=awslc as the default
// query, and nothing below passes a property string.
TEST(RsaProviderConfigTest, GeneratesSignsAndInteroperates) {
  LibCtxPtr libctx(OSSL_LIB_CTX_new());
  ASSERT_TRUE(libctx);
  ASSERT_TRUE(OSSL_PROVIDER_set_default_search_path(libctx.get(),
                                                    AWSLC_PROVIDER_MODULE_DIR));
  ASSERT_TRUE(
      OSSL_LIB_CTX_load_config(libctx.get(), AWSLC_PROVIDER_CONFIG_FILE));

  // This keygen must stay the first RSA operation on this library context. A
  // preceding operation over a default-origin key caches a default keymgmt
  // against the same empty property query, and this NULL-propquery keygen would
  // then be served by default rather than by the preference below.
  PkeyCtxPtr ctx(EVP_PKEY_CTX_new_from_name(libctx.get(), "RSA", nullptr));
  ASSERT_TRUE(ctx);
  ASSERT_GT(EVP_PKEY_keygen_init(ctx.get()), 0);
  EVP_PKEY *raw_key = nullptr;
  ASSERT_GT(EVP_PKEY_generate(ctx.get(), &raw_key), 0);
  PkeyPtr key(raw_key);
  EXPECT_EQ(kProviderName, ProviderOf(key.get()));

  MdCtxPtr sign(EVP_MD_CTX_new());
  ASSERT_TRUE(sign);
  ASSERT_TRUE(EVP_DigestSignInit_ex(sign.get(), nullptr, "SHA2-256",
                                    libctx.get(), nullptr, key.get(), nullptr));
  size_t len = 0;
  const unsigned char *message =
      reinterpret_cast<const unsigned char *>(kMessage);
  ASSERT_TRUE(
      EVP_DigestSign(sign.get(), nullptr, &len, message, sizeof(kMessage) - 1));
  std::vector<unsigned char> sig(len);
  ASSERT_TRUE(EVP_DigestSign(sign.get(), sig.data(), &len, message,
                             sizeof(kMessage) - 1));
  sig.resize(len);

  BioPtr pem(BIO_new(BIO_s_mem()));
  ASSERT_TRUE(pem);
  ASSERT_TRUE(PEM_write_bio_PrivateKey_ex(pem.get(), key.get(), nullptr,
                                          nullptr, 0, nullptr, nullptr,
                                          libctx.get(), nullptr));
  PkeyPtr decoded(PEM_read_bio_PrivateKey_ex(pem.get(), nullptr, nullptr,
                                             nullptr, libctx.get(), nullptr));
  ASSERT_TRUE(decoded);
  EXPECT_EQ("default", ProviderOf(decoded.get()));

  MdCtxPtr verify(EVP_MD_CTX_new());
  ASSERT_TRUE(verify);
  ASSERT_TRUE(EVP_DigestVerifyInit_ex(verify.get(), nullptr, "SHA2-256",
                                      libctx.get(), nullptr, decoded.get(),
                                      nullptr));
  EXPECT_EQ(1, EVP_DigestVerify(verify.get(), sig.data(), sig.size(), message,
                                sizeof(kMessage) - 1));
  ERR_clear_error();
}

}  // namespace
}  // namespace awslc_provider_test
