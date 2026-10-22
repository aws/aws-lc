// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include "test/test_fixture.h"

#include <openssl/bio.h>
#include <openssl/bn.h>
#include <openssl/core_names.h>
#include <openssl/evp.h>
#include <openssl/indicator.h>
#include <openssl/param_build.h>
#include <openssl/params.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>

#include <map>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "boundary.h"
#include "test/rsa_test_key.h"

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

constexpr const char *kRequireDefault = "provider=default";
constexpr char kMessage[] = "RSA signature";

// How the provider tags AWS-LC's reasons. The backend suite pins the values.
constexpr int kAwslcLibRsa = 4;
constexpr int kAwslcLibEvp = 6;
constexpr int kAwslcRsaBadSignature = 105;
constexpr int kAwslcEvpInvalidPssMd = 500;

// For the 2048-bit test key and SHA-256: 256 - 32 - 2.
constexpr int kMaxSaltlen = 222;

struct PkeyDeleter {
  void operator()(EVP_PKEY *pkey) const { EVP_PKEY_free(pkey); }
};
struct PkeyCtxDeleter {
  void operator()(EVP_PKEY_CTX *ctx) const { EVP_PKEY_CTX_free(ctx); }
};
struct ParamsDeleter {
  void operator()(OSSL_PARAM *params) const { OSSL_PARAM_free(params); }
};
struct BioDeleter {
  void operator()(BIO *bio) const { BIO_free(bio); }
};

using PkeyPtr = std::unique_ptr<EVP_PKEY, PkeyDeleter>;
using PkeyCtxPtr = std::unique_ptr<EVP_PKEY_CTX, PkeyCtxDeleter>;
using ParamsPtr = std::unique_ptr<OSSL_PARAM, ParamsDeleter>;
using BioPtr = std::unique_ptr<BIO, BioDeleter>;

// Control strings, applied as `openssl dgst -sigopt` applies them.
using Options = std::vector<std::pair<std::string, std::string>>;

const Options kPkcs1 = {{"rsa_padding_mode", "pkcs1"}};
const Options kPss = {{"rsa_padding_mode", "pss"}};

Options Pss(const std::string &saltlen) {
  return {{"rsa_padding_mode", "pss"}, {"rsa_pss_saltlen", saltlen}};
}

std::string ProviderOf(const EVP_PKEY *pkey) {
  const OSSL_PROVIDER *provider = EVP_PKEY_get0_provider(pkey);
  return provider == nullptr ? "<none>" : OSSL_PROVIDER_get0_name(provider);
}

std::string ProviderOf(const EVP_PKEY_CTX *ctx) {
  const OSSL_PROVIDER *provider = EVP_PKEY_CTX_get0_provider(ctx);
  return provider == nullptr ? "<none>" : OSSL_PROVIDER_get0_name(provider);
}

const unsigned char *Message() {
  return reinterpret_cast<const unsigned char *>(kMessage);
}

std::set<std::string> Names(const OSSL_PARAM *params) {
  std::set<std::string> names;
  for (const OSSL_PARAM *p = params; p != nullptr && p->key != nullptr; p++) {
    names.insert(p->key);
  }
  return names;
}

int FipsIndicator(EVP_PKEY_CTX *ctx) {
  int approved = -1;
  OSSL_PARAM params[] = {
      OSSL_PARAM_construct_int(OSSL_SIGNATURE_PARAM_FIPS_APPROVED_INDICATOR,
                               &approved),
      OSSL_PARAM_construct_end()};
  return EVP_PKEY_CTX_get_params(ctx, params) ? approved : -1;
}

class RsaSignatureTest : public ProviderTest {
 protected:
  // A default-origin key, as every loaded key is.
  PkeyPtr Decode() {
    BioPtr bio(BIO_new_mem_buf(kRsa2048Pem, -1));
    if (!bio) {
      return nullptr;
    }
    return PkeyPtr(PEM_read_bio_PrivateKey_ex(
        bio.get(), nullptr, nullptr, nullptr, libctx(), kRequireDefault));
  }

  // |pkey|'s key pair plus |extra|, imported into |type|'s key manager under
  // |propq|.
  PkeyPtr CopyInto(const EVP_PKEY *pkey, const char *type, const char *propq,
                   const std::map<std::string, std::string> &digests = {},
                   int saltlen = -1) {
    OSSL_PARAM *exported = nullptr;
    if (!EVP_PKEY_todata(pkey, EVP_PKEY_KEYPAIR, &exported)) {
      return nullptr;
    }
    ParamsPtr keypair(exported);
    OSSL_PARAM_BLD *bld = OSSL_PARAM_BLD_new();
    for (const auto &d : digests) {
      OSSL_PARAM_BLD_push_utf8_string(bld, d.first.c_str(), d.second.c_str(),
                                      0);
    }
    if (saltlen >= 0) {
      OSSL_PARAM_BLD_push_int(bld, OSSL_PKEY_PARAM_RSA_PSS_SALTLEN, saltlen);
    }
    ParamsPtr extra(OSSL_PARAM_BLD_to_param(bld));
    OSSL_PARAM_BLD_free(bld);
    ParamsPtr params(OSSL_PARAM_merge(keypair.get(), extra.get()));

    PkeyCtxPtr ctx(EVP_PKEY_CTX_new_from_name(libctx(), type, propq));
    EVP_PKEY *out = nullptr;
    if (!params || !ctx || EVP_PKEY_fromdata_init(ctx.get()) <= 0 ||
        EVP_PKEY_fromdata(ctx.get(), &out, EVP_PKEY_KEYPAIR, params.get()) <=
            0) {
      return nullptr;
    }
    return PkeyPtr(out);
  }

  // EVP_DigestSign by the signer |propq| selects, which |signer| names.
  std::vector<unsigned char> Sign(EVP_PKEY *pkey, const char *propq,
                                  const char *md, const Options &options,
                                  std::string *signer = nullptr) {
    MdCtxPtr ctx(EVP_MD_CTX_new());
    EVP_PKEY_CTX *pctx = nullptr;
    size_t len = 0;
    if (!ctx ||
        !EVP_DigestSignInit_ex(ctx.get(), &pctx, md, libctx(), propq, pkey,
                               nullptr) ||
        !Apply(pctx, options)) {
      return {};
    }
    if (signer != nullptr) {
      *signer = ProviderOf(pctx);
    }
    if (!EVP_DigestSign(ctx.get(), nullptr, &len, Message(),
                        sizeof(kMessage) - 1)) {
      return {};
    }
    std::vector<unsigned char> sig(len);
    if (!EVP_DigestSign(ctx.get(), sig.data(), &len, Message(),
                        sizeof(kMessage) - 1)) {
      return {};
    }
    sig.resize(len);
    return sig;
  }

  // EVP_DigestVerify's own return value, or -2 when setup fails.
  int Verify(EVP_PKEY *pkey, const char *propq, const char *md,
             const Options &options, const std::vector<unsigned char> &sig,
             std::string *verifier = nullptr) {
    MdCtxPtr ctx(EVP_MD_CTX_new());
    EVP_PKEY_CTX *pctx = nullptr;
    if (!ctx ||
        !EVP_DigestVerifyInit_ex(ctx.get(), &pctx, md, libctx(), propq, pkey,
                                 nullptr) ||
        !Apply(pctx, options)) {
      return -2;
    }
    if (verifier != nullptr) {
      *verifier = ProviderOf(pctx);
    }
    return EVP_DigestVerify(ctx.get(), sig.data(), sig.size(), Message(),
                            sizeof(kMessage) - 1);
  }

  static bool Apply(EVP_PKEY_CTX *pctx, const Options &options) {
    for (const auto &option : options) {
      if (EVP_PKEY_CTX_ctrl_str(pctx, option.first.c_str(),
                                option.second.c_str()) <= 0) {
        return false;
      }
    }
    return true;
  }

  PkeyCtxPtr PrehashCtx(EVP_PKEY *pkey, const char *propq) {
    return PkeyCtxPtr(EVP_PKEY_CTX_new_from_pkey(libctx(), pkey, propq));
  }

  // SHA-256 of kMessage, by default.
  std::vector<unsigned char> Digest() {
    std::vector<unsigned char> out(32);
    unsigned int len = 0;
    MdPtr md(EVP_MD_fetch(libctx(), "SHA2-256", kRequireDefault));
    if (!md || !EVP_Digest(kMessage, sizeof(kMessage) - 1, out.data(), &len,
                           md.get(), nullptr)) {
      return {};
    }
    return out;
  }
};

// The default-origin key is exported into the awslc key manager at init, and
// the signature that follows is awslc's.
TEST_F(RsaSignatureTest, DefaultOriginKeyCrossesIntoAwslcAndInteroperates) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);
  ASSERT_EQ("default", ProviderOf(key.get()));

  for (const Options *options : {&kPkcs1, &kPss}) {
    SCOPED_TRACE(options->front().second);
    std::string signer;
    std::string verifier;

    const std::vector<unsigned char> ours =
        Sign(key.get(), kRequireAwslc, "SHA2-256", *options, &signer);
    ASSERT_FALSE(ours.empty());
    EXPECT_EQ(kProviderName, signer);
    EXPECT_EQ(1, Verify(key.get(), kRequireDefault, "SHA2-256", *options, ours,
                        &verifier));
    EXPECT_EQ("default", verifier);

    const std::vector<unsigned char> theirs =
        Sign(key.get(), kRequireDefault, "SHA2-256", *options, &signer);
    ASSERT_FALSE(theirs.empty());
    EXPECT_EQ("default", signer);
    EXPECT_EQ(1, Verify(key.get(), kRequireAwslc, "SHA2-256", *options, theirs,
                        &verifier));
    EXPECT_EQ(kProviderName, verifier);
  }
  EXPECT_EQ("default", ProviderOf(key.get()));
  EXPECT_EQ(0ul, ERR_peek_error()) << "a successful signature left the queue";
}

// Each PSS parameter reaches AWS-LC: default accepts the signature only under
// exactly the parameters it was made with.
TEST_F(RsaSignatureTest, HonorsPssParameters) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);
  Options options = Pss("20");
  options.push_back({"rsa_mgf1_md", "SHA1"});

  const std::vector<unsigned char> sig =
      Sign(key.get(), kRequireAwslc, "SHA2-256", options);
  ASSERT_FALSE(sig.empty());
  EXPECT_EQ(1, Verify(key.get(), kRequireDefault, "SHA2-256", options, sig));

  Options other_mgf1 = Pss("20");
  other_mgf1.push_back({"rsa_mgf1_md", "SHA2-256"});
  EXPECT_EQ(0, Verify(key.get(), kRequireDefault, "SHA2-256", other_mgf1, sig));
  Options other_saltlen = Pss("32");
  other_saltlen.push_back({"rsa_mgf1_md", "SHA1"});
  EXPECT_EQ(0,
            Verify(key.get(), kRequireDefault, "SHA2-256", other_saltlen, sig));
  ERR_clear_error();
}

// AWS-LC has only "digest" and "auto"; the rest are resolved here.
TEST_F(RsaSignatureTest, MapsOpenSslSaltLengths) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);

  const struct {
    Options sign;
    int used;
  } kSigned[] = {
      {kPss, 32},  // OpenSSL's default, auto-digestmax.
      {Pss("digest"), 32},
      {Pss("auto"), kMaxSaltlen},
      {Pss("max"), kMaxSaltlen},
      {Pss("auto-digestmax"), 32},
      {Pss("20"), 20},
      // libcrypto's numeric spelling of "auto".
      {Pss("-2"), kMaxSaltlen},
  };
  for (const auto &c : kSigned) {
    SCOPED_TRACE(c.sign.back().second);
    const std::vector<unsigned char> sig =
        Sign(key.get(), kRequireAwslc, "SHA2-256", c.sign);
    ASSERT_FALSE(sig.empty());
    EXPECT_EQ(1, Verify(key.get(), kRequireDefault, "SHA2-256",
                        Pss(std::to_string(c.used)), sig));
  }

  const std::vector<unsigned char> max_salt =
      Sign(key.get(), kRequireDefault, "SHA2-256", Pss("max"));
  const std::vector<unsigned char> digest_salt =
      Sign(key.get(), kRequireDefault, "SHA2-256", Pss("digest"));
  ASSERT_FALSE(max_salt.empty());
  ASSERT_FALSE(digest_salt.empty());
  const struct {
    Options verify;
    int max_salt;
    int digest_salt;
  } kVerified[] = {
      {kPss, 1, 1},
      {Pss("auto"), 1, 1},
      {Pss("max"), 1, 0},
      {Pss("digest"), 0, 1},
  };
  for (const auto &c : kVerified) {
    SCOPED_TRACE(c.verify.back().second);
    EXPECT_EQ(c.max_salt,
              Verify(key.get(), kRequireAwslc, "SHA2-256", c.verify, max_salt));
    EXPECT_EQ(c.digest_salt, Verify(key.get(), kRequireAwslc, "SHA2-256",
                                    c.verify, digest_salt));
  }
  ERR_clear_error();
}

TEST_F(RsaSignatureTest, RefusesSaltLengthOutsideInt) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);
  PkeyCtxPtr ctx = PrehashCtx(key.get(), kRequireAwslc);
  ASSERT_TRUE(ctx);
  ASSERT_GT(EVP_PKEY_sign_init(ctx.get()), 0);
  ASSERT_GT(EVP_PKEY_CTX_set_rsa_padding(ctx.get(), RSA_PKCS1_PSS_PADDING), 0);

  ERR_clear_error();
  EXPECT_LE(
      EVP_PKEY_CTX_ctrl_str(ctx.get(), "rsa_pss_saltlen", "-3000000000"), 0);
  const std::vector<ErrorRecord> ours = ProviderErrors(DrainErrors());
  ASSERT_EQ(1u, ours.size());
  EXPECT_EQ((unsigned long)AWSLC_PROV_R_INVALID_PARAMETER, ours[0].reason());
  EXPECT_EQ(OSSL_SIGNATURE_PARAM_PSS_SALTLEN, ours[0].data);
}

// PSS padding, the only one an RSA-PSS key has, waits for a digest before the
// salt length resolves.
TEST_F(RsaSignatureTest, InitsUnrestrictedRsaPssKeyBeforeDigest) {
  PkeyPtr rsa = Decode();
  ASSERT_TRUE(rsa);
  PkeyPtr ours = CopyInto(rsa.get(), "RSA-PSS", kRequireAwslc);
  ASSERT_TRUE(ours);
  const std::vector<unsigned char> digest = Digest();
  ASSERT_FALSE(digest.empty());

  PkeyCtxPtr sign = PrehashCtx(ours.get(), kRequireAwslc);
  ASSERT_TRUE(sign);
  ASSERT_GT(EVP_PKEY_sign_init(sign.get()), 0);
  ASSERT_GT(EVP_PKEY_CTX_set_signature_md(sign.get(), EVP_sha256()), 0);
  std::vector<unsigned char> sig(256);
  size_t len = sig.size();
  ASSERT_GT(
      EVP_PKEY_sign(sign.get(), sig.data(), &len, digest.data(), digest.size()),
      0);
  sig.resize(len);
  EXPECT_EQ(1, Verify(rsa.get(), kRequireDefault, "SHA2-256", Pss("32"), sig));
  EXPECT_EQ(0ul, ERR_peek_error());
}

// The PKCS#1 v1.5 OIDs AWS-LC has no NID for, by one of them.
TEST_F(RsaSignatureTest, ReportsAlgorithmIdAwslcHasNoNidFor) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);
  auto algorithm_id = [&](const char *propq) {
    std::vector<unsigned char> out(128);
    OSSL_PARAM params[] = {
        OSSL_PARAM_construct_octet_string(OSSL_SIGNATURE_PARAM_ALGORITHM_ID,
                                          out.data(), out.size()),
        OSSL_PARAM_construct_end()};
    PkeyCtxPtr ctx = PrehashCtx(key.get(), propq);
    if (!ctx || EVP_PKEY_sign_init(ctx.get()) <= 0 ||
        EVP_PKEY_CTX_set_signature_md(ctx.get(), EVP_sha3_256()) <= 0 ||
        !EVP_PKEY_CTX_get_params(ctx.get(), params)) {
      return std::vector<unsigned char>();
    }
    out.resize(params[0].return_size);
    return out;
  };
  const std::vector<unsigned char> theirs = algorithm_id(kRequireDefault);
  ASSERT_FALSE(theirs.empty());
  EXPECT_EQ(theirs, algorithm_id(kRequireAwslc));
  EXPECT_EQ(0ul, ERR_peek_error());
}

// The parameters read back as default reports them, including the DER
// AlgorithmIdentifier that X.509 and CMS sign under.
TEST_F(RsaSignatureTest, ReportsParametersLikeDefault) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);

  struct Report {
    int padding = 0;
    int saltlen = 0;
    std::string padding_name;
    std::string saltlen_name;
    std::string digest;
    std::string mgf1_digest;
    std::vector<unsigned char> algorithm_id;
  };
  auto report = [&](const char *propq, bool pss) {
    Report out;
    MdCtxPtr ctx(EVP_MD_CTX_new());
    EVP_PKEY_CTX *pctx = nullptr;
    if (!ctx || !EVP_DigestSignInit_ex(ctx.get(), &pctx, "SHA2-256", libctx(),
                                       propq, key.get(), nullptr)) {
      return out;
    }
    if (pss &&
        (EVP_PKEY_CTX_set_rsa_padding(pctx, RSA_PKCS1_PSS_PADDING) <= 0 ||
         EVP_PKEY_CTX_set_rsa_mgf1_md_name(pctx, "SHA2-384", nullptr) <= 0 ||
         EVP_PKEY_CTX_set_rsa_pss_saltlen(pctx, RSA_PSS_SALTLEN_AUTO) <= 0)) {
      return out;
    }
    char padding_name[16] = {0};
    char saltlen_name[16] = {0};
    char digest[32] = {0};
    char mgf1_digest[32] = {0};
    unsigned char aid[128];
    OSSL_PARAM params[] = {
        OSSL_PARAM_construct_int(OSSL_SIGNATURE_PARAM_PAD_MODE, &out.padding),
        OSSL_PARAM_construct_int(OSSL_SIGNATURE_PARAM_PSS_SALTLEN,
                                 &out.saltlen),
        OSSL_PARAM_construct_utf8_string(OSSL_SIGNATURE_PARAM_DIGEST, digest,
                                         sizeof(digest)),
        OSSL_PARAM_construct_utf8_string(OSSL_SIGNATURE_PARAM_MGF1_DIGEST,
                                         mgf1_digest, sizeof(mgf1_digest)),
        OSSL_PARAM_construct_octet_string(OSSL_SIGNATURE_PARAM_ALGORITHM_ID,
                                          aid, sizeof(aid)),
        OSSL_PARAM_construct_end()};
    OSSL_PARAM names[] = {
        OSSL_PARAM_construct_utf8_string(OSSL_SIGNATURE_PARAM_PAD_MODE,
                                         padding_name, sizeof(padding_name)),
        OSSL_PARAM_construct_utf8_string(OSSL_SIGNATURE_PARAM_PSS_SALTLEN,
                                         saltlen_name, sizeof(saltlen_name)),
        OSSL_PARAM_construct_end()};
    if (!EVP_PKEY_CTX_get_params(pctx, params) ||
        !EVP_PKEY_CTX_get_params(pctx, names)) {
      return out;
    }
    out.padding_name = padding_name;
    out.saltlen_name = saltlen_name;
    out.digest = digest;
    out.mgf1_digest = mgf1_digest;
    out.algorithm_id.assign(aid, aid + params[4].return_size);
    return out;
  };

  for (bool pss : {false, true}) {
    SCOPED_TRACE(pss ? "PSS" : "PKCS#1 v1.5");
    const Report ours = report(kRequireAwslc, pss);
    const Report theirs = report(kRequireDefault, pss);
    ASSERT_FALSE(theirs.algorithm_id.empty());
    EXPECT_EQ(theirs.algorithm_id, ours.algorithm_id);
    EXPECT_EQ(theirs.padding, ours.padding);
    EXPECT_EQ(theirs.padding_name, ours.padding_name);
    EXPECT_EQ(theirs.digest, ours.digest);
    if (pss) {
      EXPECT_EQ(theirs.saltlen, ours.saltlen);
      EXPECT_EQ(theirs.saltlen_name, ours.saltlen_name);
      EXPECT_EQ(theirs.mgf1_digest, ours.mgf1_digest);
    }
  }
  EXPECT_EQ(0ul, ERR_peek_error());
}

TEST_F(RsaSignatureTest, DeclaresParamsByOperation) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);
  const std::set<std::string> fixed = {OSSL_SIGNATURE_PARAM_PAD_MODE,
                                       OSSL_SIGNATURE_PARAM_MGF1_DIGEST,
                                       OSSL_SIGNATURE_PARAM_PSS_SALTLEN};
  std::set<std::string> settable = fixed;
  settable.insert(OSSL_SIGNATURE_PARAM_DIGEST);

  PkeyCtxPtr prehash = PrehashCtx(key.get(), kRequireAwslc);
  ASSERT_TRUE(prehash);
  ASSERT_GT(EVP_PKEY_sign_init(prehash.get()), 0);
  EXPECT_EQ(settable, Names(EVP_PKEY_CTX_settable_params(prehash.get())));
  EXPECT_EQ(
      (std::set<std::string>{
          OSSL_SIGNATURE_PARAM_ALGORITHM_ID, OSSL_SIGNATURE_PARAM_PAD_MODE,
          OSSL_SIGNATURE_PARAM_DIGEST, OSSL_SIGNATURE_PARAM_MGF1_DIGEST,
          OSSL_SIGNATURE_PARAM_PSS_SALTLEN,
          OSSL_SIGNATURE_PARAM_FIPS_APPROVED_INDICATOR}),
      Names(EVP_PKEY_CTX_gettable_params(prehash.get())));

  MdCtxPtr ctx(EVP_MD_CTX_new());
  EVP_PKEY_CTX *pctx = nullptr;
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(EVP_DigestSignInit_ex(ctx.get(), &pctx, "SHA2-256", libctx(),
                                    kRequireAwslc, key.get(), nullptr));
  EXPECT_EQ(fixed, Names(EVP_PKEY_CTX_settable_params(pctx)));

  // A digest operation's digest is fixed.
  ERR_clear_error();
  OSSL_PARAM other[] = {
      OSSL_PARAM_construct_utf8_string(OSSL_SIGNATURE_PARAM_DIGEST,
                                       const_cast<char *>("SHA2-384"), 0),
      OSSL_PARAM_construct_end()};
  EXPECT_FALSE(EVP_PKEY_CTX_set_params(pctx, other));
  const std::vector<ErrorRecord> ours = ProviderErrors(DrainErrors());
  ASSERT_EQ(1u, ours.size());
  EXPECT_EQ((unsigned long)AWSLC_PROV_R_INVALID_PARAMETER, ours[0].reason());
  EXPECT_EQ(OSSL_SIGNATURE_PARAM_DIGEST, ours[0].data);
}

// The prehash slots: a raw PKCS#1 v1.5 signature with no digest, a signature
// over a caller's digest, and recovery of what was signed.
TEST_F(RsaSignatureTest, SignsAndRecoversThroughPrehashSlots) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);
  const std::vector<unsigned char> digest = Digest();
  ASSERT_FALSE(digest.empty());

  PkeyCtxPtr raw = PrehashCtx(key.get(), kRequireAwslc);
  ASSERT_TRUE(raw);
  ASSERT_GT(EVP_PKEY_sign_init(raw.get()), 0);
  EXPECT_EQ(kProviderName, ProviderOf(raw.get()));
  size_t len = 0;
  ASSERT_GT(
      EVP_PKEY_sign(raw.get(), nullptr, &len, digest.data(), digest.size()), 0);
  std::vector<unsigned char> raw_sig(len);
  ASSERT_GT(EVP_PKEY_sign(raw.get(), raw_sig.data(), &len, digest.data(),
                          digest.size()),
            0);
  raw_sig.resize(len);

  PkeyCtxPtr recover = PrehashCtx(key.get(), kRequireDefault);
  ASSERT_TRUE(recover);
  ASSERT_GT(EVP_PKEY_verify_recover_init(recover.get()), 0);
  std::vector<unsigned char> recovered(256);
  len = recovered.size();
  ASSERT_GT(EVP_PKEY_verify_recover(recover.get(), recovered.data(), &len,
                                    raw_sig.data(), raw_sig.size()),
            0);
  recovered.resize(len);
  EXPECT_EQ(digest, recovered);

  PkeyCtxPtr sign = PrehashCtx(key.get(), kRequireAwslc);
  ASSERT_TRUE(sign);
  ASSERT_GT(EVP_PKEY_sign_init(sign.get()), 0);
  ASSERT_GT(EVP_PKEY_CTX_set_signature_md(sign.get(), EVP_sha256()), 0);
  std::vector<unsigned char> sig(256);
  len = sig.size();
  ASSERT_GT(
      EVP_PKEY_sign(sign.get(), sig.data(), &len, digest.data(), digest.size()),
      0);
  sig.resize(len);
  EXPECT_EQ(1, Verify(key.get(), kRequireDefault, "SHA2-256", kPkcs1, sig));

  PkeyCtxPtr ours = PrehashCtx(key.get(), kRequireAwslc);
  ASSERT_TRUE(ours);
  ASSERT_GT(EVP_PKEY_verify_recover_init(ours.get()), 0);
  ASSERT_GT(EVP_PKEY_CTX_set_signature_md(ours.get(), EVP_sha256()), 0);
  recovered.assign(256, 0);
  len = recovered.size();
  ASSERT_GT(EVP_PKEY_verify_recover(ours.get(), recovered.data(), &len,
                                    sig.data(), sig.size()),
            0);
  recovered.resize(len);
  EXPECT_EQ(digest, recovered);
  EXPECT_EQ(0ul, ERR_peek_error());
}

// AWS-LC sees the caller's capacity, not the key size, so a short buffer fails
// with nothing written past it.
TEST_F(RsaSignatureTest, RefusesUndersizedOutput) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);
  const std::vector<unsigned char> digest = Digest();
  ASSERT_FALSE(digest.empty());
  const size_t kShort = 255;
  const unsigned char kCanary = 0xa5;

  MdCtxPtr ctx(EVP_MD_CTX_new());
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(EVP_DigestSignInit_ex(ctx.get(), nullptr, "SHA2-256", libctx(),
                                    kRequireAwslc, key.get(), nullptr));
  ASSERT_TRUE(EVP_DigestSignUpdate(ctx.get(), Message(), sizeof(kMessage) - 1));
  std::vector<unsigned char> out(kShort + 16, kCanary);
  size_t len = kShort;
  EXPECT_FALSE(EVP_DigestSignFinal(ctx.get(), out.data(), &len));
  EXPECT_EQ(std::vector<unsigned char>(16, kCanary),
            std::vector<unsigned char>(out.begin() + kShort, out.end()));

  PkeyCtxPtr sign = PrehashCtx(key.get(), kRequireAwslc);
  ASSERT_TRUE(sign);
  ASSERT_GT(EVP_PKEY_sign_init(sign.get()), 0);
  out.assign(kShort + 16, kCanary);
  len = kShort;
  EXPECT_LE(
      EVP_PKEY_sign(sign.get(), out.data(), &len, digest.data(), digest.size()),
      0);
  EXPECT_EQ(std::vector<unsigned char>(16, kCanary),
            std::vector<unsigned char>(out.begin() + kShort, out.end()));
  EXPECT_FALSE(ProviderErrors(DrainErrors()).empty());
}

int g_unapproved_calls = 0;

int CountUnapproved(const char *, const char *, const OSSL_PARAM[]) {
  g_unapproved_calls++;
  return 1;
}

// Only EVP_DigestSign* and EVP_DigestVerify* credit AWS-LC's indicator; the
// prehash slots report unapproved whatever its counter does.
TEST_F(RsaSignatureTest, ReportsFipsIndicatorByEntryPoint) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);
  const std::vector<unsigned char> digest = Digest();
  ASSERT_FALSE(digest.empty());
  g_unapproved_calls = 0;
  OSSL_INDICATOR_set_callback(libctx(), CountUnapproved);

  MdCtxPtr ctx(EVP_MD_CTX_new());
  EVP_PKEY_CTX *pctx = nullptr;
  ASSERT_TRUE(ctx);
  ASSERT_TRUE(EVP_DigestSignInit_ex(ctx.get(), &pctx, "SHA2-256", libctx(),
                                    kRequireAwslc, key.get(), nullptr));
  std::vector<unsigned char> sig(256);
  size_t len = sig.size();
  ASSERT_TRUE(EVP_DigestSign(ctx.get(), sig.data(), &len, Message(),
                             sizeof(kMessage) - 1));
  EXPECT_EQ(kFipsBuild, FipsIndicator(pctx));
  EXPECT_EQ(0, g_unapproved_calls);

  PkeyCtxPtr sign = PrehashCtx(key.get(), kRequireAwslc);
  ASSERT_TRUE(sign);
  ASSERT_GT(EVP_PKEY_sign_init(sign.get()), 0);
  ASSERT_GT(EVP_PKEY_CTX_set_signature_md(sign.get(), EVP_sha256()), 0);
  len = sig.size();
  ASSERT_GT(
      EVP_PKEY_sign(sign.get(), sig.data(), &len, digest.data(), digest.size()),
      0);
  EXPECT_EQ(0, FipsIndicator(sign.get()));
  EXPECT_EQ(kFipsBuild, g_unapproved_calls);

  PkeyCtxPtr verify = PrehashCtx(key.get(), kRequireAwslc);
  ASSERT_TRUE(verify);
  ASSERT_GT(EVP_PKEY_verify_init(verify.get()), 0);
  ASSERT_GT(EVP_PKEY_CTX_set_signature_md(verify.get(), EVP_sha256()), 0);
  EXPECT_EQ(1, EVP_PKEY_verify(verify.get(), sig.data(), len, digest.data(),
                               digest.size()));
  EXPECT_EQ(0, FipsIndicator(verify.get()));
  EXPECT_EQ(2 * kFipsBuild, g_unapproved_calls);
  OSSL_INDICATOR_set_callback(libctx(), nullptr);
}

// A wrong signature is 0, not -1, and the reason is AWS-LC's, filed under the
// provider's private library.
TEST_F(RsaSignatureTest, MismatchReturnsZeroWithAwslcReason) {
  PkeyPtr key = Decode();
  ASSERT_TRUE(key);
  // Its DigestInfo is longer than SHA-256's, which AWS-LC reports as
  // RSA_R_BAD_SIGNATURE.
  const std::vector<unsigned char> sha384 =
      Sign(key.get(), kRequireAwslc, "SHA2-384", kPkcs1);
  ASSERT_FALSE(sha384.empty());

  ERR_clear_error();
  EXPECT_EQ(0, Verify(key.get(), kRequireAwslc, "SHA2-256", kPkcs1, sha384));
  const std::vector<ErrorRecord> all = DrainErrors();
  const std::vector<ErrorRecord> ours = ProviderErrors(all);
  ASSERT_EQ(1u, ours.size());
  EXPECT_EQ((unsigned long)AWSLC_PROV_ERROR_REASON(kAwslcLibRsa,
                                                   kAwslcRsaBadSignature),
            ours[0].reason());
  EXPECT_NE(std::string::npos, ours[0].data.find("BAD_SIGNATURE"))
      << ours[0].data;
  EXPECT_EQ(all.size(), ours.size()) << "a record escaped the private library";

  const std::vector<unsigned char> digest = Digest();
  PkeyCtxPtr verify = PrehashCtx(key.get(), kRequireAwslc);
  ASSERT_TRUE(verify);
  ASSERT_GT(EVP_PKEY_verify_init(verify.get()), 0);
  ASSERT_GT(EVP_PKEY_CTX_set_signature_md(verify.get(), EVP_sha256()), 0);
  EXPECT_EQ(0, EVP_PKEY_verify(verify.get(), sha384.data(), sha384.size(),
                               digest.data(), digest.size()));
  EXPECT_EQ(1u, ProviderErrors(DrainErrors()).size());
}


// AWS-LC, not the provider, holds a restricted key to its digest.
TEST_F(RsaSignatureTest, AwslcEnforcesPssRestrictions) {
  PkeyPtr rsa = Decode();
  ASSERT_TRUE(rsa);
  PkeyPtr theirs = CopyInto(rsa.get(), "RSA-PSS", kRequireDefault,
                            {{OSSL_PKEY_PARAM_RSA_DIGEST, "SHA2-256"},
                             {OSSL_PKEY_PARAM_RSA_MGF1_DIGEST, "SHA2-256"}},
                            32);
  ASSERT_TRUE(theirs);
  PkeyPtr ours = CopyInto(theirs.get(), "RSA-PSS", kRequireAwslc);
  ASSERT_TRUE(ours);

  // The mandatory digest is the one libcrypto asks for when none is named, and
  // PSS is the key's only padding.
  std::string signer;
  const std::vector<unsigned char> sig =
      Sign(ours.get(), kRequireAwslc, nullptr, {}, &signer);
  ASSERT_FALSE(sig.empty());
  EXPECT_EQ(kProviderName, signer);
  EXPECT_EQ(1, Verify(rsa.get(), kRequireDefault, "SHA2-256", Pss("32"), sig));

  ERR_clear_error();
  EXPECT_TRUE(Sign(ours.get(), kRequireAwslc, "SHA2-384", {}).empty());
  const std::vector<ErrorRecord> refused = ProviderErrors(DrainErrors());
  ASSERT_FALSE(refused.empty());
  EXPECT_EQ((unsigned long)AWSLC_PROV_ERROR_REASON(kAwslcLibEvp,
                                                   kAwslcEvpInvalidPssMd),
            refused[0].reason());

  EXPECT_TRUE(Sign(ours.get(), kRequireAwslc, "SHA2-256", kPkcs1).empty());
  EXPECT_FALSE(ProviderErrors(DrainErrors()).empty());
}



// Under the deployed preference the first fetch to fill the empty-query RSA
// key manager slot keeps it, whichever provider it names. An RSA encryption,
// which awslc does not serve, stores default's there, and an unqualified keygen
// then goes to default. The signature slot is separate, so signing still goes
// to awslc. This pins libcrypto's first-writer-wins cache, so a change in it
// fails here rather than as flakiness in attribution tests.
TEST(RsaSignatureConfigTest, PinsOrderDependentPreference) {
  LibCtxPtr libctx(OSSL_LIB_CTX_new());
  ASSERT_TRUE(libctx);
  ASSERT_TRUE(OSSL_PROVIDER_set_default_search_path(libctx.get(),
                                                    AWSLC_PROVIDER_MODULE_DIR));
  ASSERT_TRUE(
      OSSL_LIB_CTX_load_config(libctx.get(), AWSLC_PROVIDER_CONFIG_FILE));

  BioPtr bio(BIO_new_mem_buf(kRsa2048Pem, -1));
  ASSERT_TRUE(bio);
  PkeyPtr decoded(PEM_read_bio_PrivateKey_ex(bio.get(), nullptr, nullptr,
                                             nullptr, libctx.get(), nullptr));
  ASSERT_TRUE(decoded);

  PkeyCtxPtr encrypt(
      EVP_PKEY_CTX_new_from_pkey(libctx.get(), decoded.get(), nullptr));
  ASSERT_TRUE(encrypt);
  ASSERT_GT(EVP_PKEY_encrypt_init(encrypt.get()), 0);
  ASSERT_EQ("default", ProviderOf(encrypt.get()));

  PkeyCtxPtr keygen(EVP_PKEY_CTX_new_from_name(libctx.get(), "RSA", nullptr));
  ASSERT_TRUE(keygen);
  ASSERT_GT(EVP_PKEY_keygen_init(keygen.get()), 0);
  EVP_PKEY *raw = nullptr;
  ASSERT_GT(EVP_PKEY_generate(keygen.get(), &raw), 0);
  PkeyPtr generated(raw);
  EXPECT_EQ("default", ProviderOf(generated.get()));

  MdCtxPtr sign(EVP_MD_CTX_new());
  EVP_PKEY_CTX *pctx = nullptr;
  ASSERT_TRUE(sign);
  ASSERT_TRUE(EVP_DigestSignInit_ex(sign.get(), &pctx, "SHA2-256", libctx.get(),
                                    nullptr, decoded.get(), nullptr));
  EXPECT_EQ(kProviderName, ProviderOf(pctx));
  ERR_clear_error();
}

}  // namespace
}  // namespace awslc_provider_test
