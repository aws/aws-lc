// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#include <functional>
#include <initializer_list>
#include <map>
#include <string>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include <openssl/digest.h>
#include <openssl/nid.h>
#include <openssl/rand.h>
#include <openssl/service_indicator.h>

#include "../../test/file_test.h"
#include "../../test/test_util.h"
#include "../sha/internal.h"
#include "./internal.h"

// SLH-DSA signing is slow (hundreds of milliseconds per signature for the
// "s" parameter sets) and crypto_test also runs under valgrind and SDE, so
// these tests keep the number of signing operations to a minimum. The full set
// of ACVP signature generation vectors runs in DISABLED_ACVPSigGenAll, which
// util/all_tests.json runs natively only.

namespace {

struct SLHDSAParamSet {
  const char name[16];
  const SLHDSA_PARAMS *(*params)(void);
  size_t public_key_bytes;
  size_t private_key_bytes;
  size_t signature_bytes;
  size_t seed_bytes;
};

const SLHDSAParamSet kParamSets[] = {
    {"SHAKE_128S", slh_dsa_shake_128s_params,
     SLHDSA_SHAKE_128S_PUBLIC_KEY_BYTES, SLHDSA_SHAKE_128S_PRIVATE_KEY_BYTES,
     SLHDSA_SHAKE_128S_SIGNATURE_BYTES, SLHDSA_SHAKE_128S_SEED_BYTES},
    {"SHAKE_192S", slh_dsa_shake_192s_params,
     SLHDSA_SHAKE_192S_PUBLIC_KEY_BYTES, SLHDSA_SHAKE_192S_PRIVATE_KEY_BYTES,
     SLHDSA_SHAKE_192S_SIGNATURE_BYTES, SLHDSA_SHAKE_192S_SEED_BYTES},
    {"SHAKE_256S", slh_dsa_shake_256s_params,
     SLHDSA_SHAKE_256S_PUBLIC_KEY_BYTES, SLHDSA_SHAKE_256S_PRIVATE_KEY_BYTES,
     SLHDSA_SHAKE_256S_SIGNATURE_BYTES, SLHDSA_SHAKE_256S_SEED_BYTES},
};

// PrehashNID returns the pre-hash function with ACVP name |name|.
int PrehashNID(const std::string &name) {
  return name == "SHAKE-128"   ? NID_shake128
         : name == "SHAKE-256" ? NID_shake256
                               : NID_undef;
}

// ExternalMessage splits M' for |iface| ("internal", "pure" or "prehash",
// with pre-hash function |hash|) into the prefix and message passed to
// |slh_dsa_sign_internal| (FIPS 205, Algorithms 22 and 23). This deliberately
// does not share code with the library, which builds M' itself.
void ExternalMessage(std::vector<uint8_t> *pre, std::vector<uint8_t> *m,
                     const std::string &iface, const std::string &hash,
                     const std::vector<uint8_t> &msg,
                     const std::vector<uint8_t> &ctx) {
  pre->clear();
  *m = msg;
  if (iface == "internal") {
    return;
  }
  ASSERT_TRUE(iface == "pure" || iface == "prehash");
  ASSERT_LE(ctx.size(), 255u);
  pre->push_back(iface == "prehash" ? 1 : 0);
  pre->push_back(static_cast<uint8_t>(ctx.size()));
  pre->insert(pre->end(), ctx.begin(), ctx.end());
  if (iface == "prehash") {
    const int hash_nid = PrehashNID(hash);
    ASSERT_NE(hash_nid, NID_undef);
    // The DER encoding of 2.16.840.1.101.3.4.2.11 (SHAKE128) or .12
    // (SHAKE256), then SHAKE128(M, 256) or SHAKE256(M, 512) (FIPS 205,
    // Algorithm 23, lines 15-20).
    const uint8_t oid[] = {
        0x06,
        0x09,
        0x60,
        0x86,
        0x48,
        0x01,
        0x65,
        0x03,
        0x04,
        0x02,
        static_cast<uint8_t>(hash_nid == NID_shake128 ? 0x0b : 0x0c)};
    pre->insert(pre->end(), oid, oid + sizeof(oid));
    if (hash_nid == NID_shake128) {
      m->resize(32);
      SHAKE128(msg.data(), msg.size(), m->data(), m->size());
    } else {
      m->resize(64);
      SHAKE256(msg.data(), msg.size(), m->data(), m->size());
    }
  }
}

class SLHDSATest : public testing::TestWithParam<SLHDSAParamSet> {
 protected:
  const SLHDSA_PARAMS *params() const { return GetParam().params(); }
  size_t pk_len() const { return slh_dsa_public_key_bytes(params()); }
  size_t sk_len() const { return slh_dsa_private_key_bytes(params()); }
  size_t sig_len() const { return slh_dsa_signature_bytes(params()); }
  size_t seed_len() const { return slh_dsa_seed_bytes(params()); }
  size_t n() const { return params()->n; }

  std::string KATPath(const char *mode) const {
    return std::string("crypto/fipsmodule/slh_dsa/kat/SLHDSA_") +
           GetParam().name + "_ACVP_" + mode + ".txt";
  }

  void GenerateKey(std::vector<uint8_t> *pk, std::vector<uint8_t> *sk) {
    pk->resize(pk_len());
    sk->resize(sk_len());
    ASSERT_TRUE(slh_dsa_keypair(params(), pk->data(), pk->size(), sk->data(),
                                sk->size()));
  }

  // SignInternal signs |pre| || |msg| with |slh_dsa_sign_internal|. An empty
  // |addrnd| selects deterministic signing.
  int SignInternal(std::vector<uint8_t> *sig, const std::vector<uint8_t> &sk,
                   const uint8_t *pre, size_t pre_len, const uint8_t *msg,
                   size_t msg_len, const std::vector<uint8_t> &addrnd) {
    sig->resize(sig_len());
    return slh_dsa_sign_internal(
        params(), sig->data(), sig->size(), sk.data(), sk.size(), pre, pre_len,
        msg, msg_len, addrnd.empty() ? nullptr : addrnd.data(), addrnd.size());
  }

  int VerifyInternal(const std::vector<uint8_t> &sig,
                     const std::vector<uint8_t> &pk, const uint8_t *pre,
                     size_t pre_len, const uint8_t *msg, size_t msg_len) {
    return slh_dsa_verify_internal(params(), sig.data(), sig.size(), pk.data(),
                                   pk.size(), pre, pre_len, msg, msg_len);
  }

  // Signing is slow, and much slower under valgrind and SDE, so tests of the
  // API rather than of the parameter set sign with SLH-DSA-SHAKE-128s only.
  // Every parameter set is still signed by |ACVPSigGen| and |PureSignVerify|.
  bool Is128s() const { return n() == 16; }

  // PrehashSupported returns whether the pre-hash function with ACVP name
  // |hash| is supported for the parameter set. SHAKE128 is only for
  // SLH-DSA-SHAKE-128s (FIPS 205, Section 10.2.2).
  bool PrehashSupported(const std::string &hash) const {
    return slh_dsa_prehash_digest_bytes(params(), PrehashNID(hash)) != 0;
  }

  // RunACVPSigGen verifies every signature generation vector through the
  // interface it targets, which checks the library's own construction of M'.
  // It also signs up to |max_signs| deterministic and |max_signs| hedged
  // vectors with |slh_dsa_sign_internal| and a prefix built by
  // |ExternalMessage|, because the library's external signing functions always
  // use fresh randomness. Pre-hash vectors that the parameter set rejects are
  // not signed.
  void RunACVPKeyGen(size_t max_vectors);

  void RunACVPSigGen(size_t max_signs) {
    std::map<bool, size_t> counts;
    FileTestGTest(KATPath("sigGen").c_str(), [&](FileTest *t) {
      std::string tc_id, iface, hash;
      std::vector<uint8_t> sk, msg, ctx, addrnd, expected_sig;
      ASSERT_TRUE(t->GetAttribute(&tc_id, "tcId"));
      ASSERT_TRUE(t->GetAttribute(&iface, "interface"));
      ASSERT_TRUE(t->GetBytes(&sk, "sk"));
      ASSERT_TRUE(t->GetBytes(&msg, "msg"));
      if (iface != "internal") {
        ASSERT_TRUE(t->GetBytes(&ctx, "ctx"));
      }
      if (iface == "prehash") {
        ASSERT_TRUE(t->GetAttribute(&hash, "hash"));
      }
      ASSERT_TRUE(t->GetBytes(&addrnd, "addrnd"));
      ASSERT_TRUE(t->GetBytes(&expected_sig, "sig"));
      // An empty addrnd selects deterministic signing.
      ASSERT_TRUE(addrnd.empty() || addrnd.size() == n());

      // Every expected signature verifies through the interface that the
      // vector targets, which builds M' itself. Unlike signing, this is cheap.
      ASSERT_EQ(sk.size(), sk_len());
      const std::vector<uint8_t> pk(sk.begin() + 2 * n(), sk.end());
      if (iface == "internal") {
        EXPECT_TRUE(VerifyInternal(expected_sig, pk, nullptr, 0, msg.data(),
                                   msg.size()));
      } else if (iface == "pure") {
        EXPECT_TRUE(slh_dsa_verify(
            params(), expected_sig.data(), expected_sig.size(), pk.data(),
            pk.size(), msg.data(), msg.size(), ctx.data(), ctx.size()));
      } else {
        // SHAKE128 is rejected for parameter sets above category 1.
        EXPECT_EQ(slh_dsa_prehash_verify(
                      params(), expected_sig.data(), expected_sig.size(),
                      pk.data(), pk.size(), PrehashNID(hash), msg.data(),
                      msg.size(), ctx.data(), ctx.size()),
                  PrehashSupported(hash) ? 1 : 0);
      }

      if ((iface == "prehash" && !PrehashSupported(hash)) ||
          counts[addrnd.empty()]++ >= max_signs) {
        return;
      }

      std::vector<uint8_t> pre, m, sig;
      ASSERT_NO_FATAL_FAILURE(ExternalMessage(&pre, &m, iface, hash, msg, ctx));
      ASSERT_TRUE(SignInternal(&sig, sk, pre.data(), pre.size(), m.data(),
                               m.size(), addrnd));
      EXPECT_EQ(Bytes(sig), Bytes(expected_sig));
    });
  }
};

INSTANTIATE_TEST_SUITE_P(
    All, SLHDSATest, testing::ValuesIn(kParamSets),
    [](const testing::TestParamInfo<SLHDSAParamSet> &info) {
      return std::string(info.param.name);
    });

// DISABLED_SLHDSASlowTest holds the tests that generate keys or sign many
// times. They are disabled by default, and util/all_tests.json runs them
// natively, but not under valgrind or SDE, where they would take hours.
// |SLHDSATest| still generates a key and signs with every parameter set.
class DISABLED_SLHDSASlowTest : public SLHDSATest {};

INSTANTIATE_TEST_SUITE_P(
    All, DISABLED_SLHDSASlowTest, testing::ValuesIn(kParamSets),
    [](const testing::TestParamInfo<SLHDSAParamSet> &info) {
      return std::string(info.param.name);
    });

// FIPS 205, Algorithm 1: gen_len2.
uint32_t GenLen2(uint32_t n, uint32_t lg_w) {
  const uint32_t w = 1u << lg_w;
  const uint32_t len1 = (8 * n + lg_w - 1) / lg_w;
  const uint32_t max_checksum = len1 * (w - 1);
  uint32_t len2 = 1;
  uint32_t capacity = w;
  while (capacity <= max_checksum) {
    len2++;
    capacity *= w;
  }
  return len2;
}

TEST_P(SLHDSATest, Parameters) {
  const SLHDSA_PARAMS *p = params();
  EXPECT_EQ(p->len1, (8 * p->n + p->lg_w - 1) / p->lg_w);
  EXPECT_EQ(p->len2, GenLen2(p->n, p->lg_w));
  EXPECT_EQ(p->h, p->d * p->hp);
  EXPECT_EQ(p->m,
            (p->k * p->a + 7) / 8 + (p->h - p->hp + 7) / 8 + (p->hp + 7) / 8);
  EXPECT_LE(p->n, (uint32_t)SLHDSA_MAX_N);
  EXPECT_LE(slh_dsa_wots_len(p), (uint32_t)SLHDSA_MAX_LEN);
  EXPECT_LE(p->hp, (uint32_t)SLHDSA_MAX_HP);
  EXPECT_LE(p->a, (uint32_t)SLHDSA_MAX_A);
  EXPECT_LE(p->k, (uint32_t)SLHDSA_MAX_K);
  EXPECT_LE(p->m, (uint32_t)SLHDSA_MAX_M);

  EXPECT_EQ(pk_len(), GetParam().public_key_bytes);
  EXPECT_EQ(sk_len(), GetParam().private_key_bytes);
  EXPECT_EQ(sig_len(), GetParam().signature_bytes);
  EXPECT_EQ(seed_len(), GetParam().seed_bytes);
  EXPECT_LE(sig_len(), (size_t)SLHDSA_MAX_SIGNATURE_BYTES);
}

// The hash functions are internal to the FIPS module and are not exported
// from the shared library.
#if !defined(BORINGSSL_SHARED_LIBRARY)
// SHAKE256Of returns SHAKE256 of the concatenation of |parts|, |out_len| bytes
// long.
std::vector<uint8_t> SHAKE256Of(
    std::initializer_list<std::vector<uint8_t>> parts, size_t out_len) {
  bssl::ScopedEVP_MD_CTX ctx;
  EXPECT_TRUE(EVP_DigestInit(ctx.get(), EVP_shake256()));
  for (const auto &part : parts) {
    EXPECT_TRUE(EVP_DigestUpdate(ctx.get(), part.data(), part.size()));
  }
  std::vector<uint8_t> out(out_len);
  EXPECT_TRUE(EVP_DigestFinalXOF(ctx.get(), out.data(), out.size()));
  return out;
}

// Pattern returns |len| bytes that differ for each |seed|.
std::vector<uint8_t> Pattern(uint8_t seed, size_t len) {
  std::vector<uint8_t> out(len);
  for (size_t i = 0; i < len; i++) {
    out[i] = static_cast<uint8_t>(seed + 31 * i);
  }
  return out;
}

// The tweakable hash functions and PRFs match their definitions in FIPS 205,
// Section 11.1, computed with the SHAKE256 API.
TEST_P(SLHDSATest, HashFunctions) {
  const size_t n = this->n();
  SLHDSA_STATE state;
  OPENSSL_memset(&state, 0, sizeof(state));
  state.params = params();
  const std::vector<uint8_t> pk_seed = Pattern(1, n), sk_seed = Pattern(2, n),
                             sk_prf = Pattern(3, n), pk_root = Pattern(4, n),
                             adrs = Pattern(5, SLHDSA_ADRS_BYTES);
  OPENSSL_memcpy(state.pk_seed, pk_seed.data(), n);
  OPENSSL_memcpy(state.sk_seed, sk_seed.data(), n);
  OPENSSL_memcpy(state.sk_prf, sk_prf.data(), n);
  OPENSSL_memcpy(state.pk_root, pk_root.data(), n);
  std::vector<uint8_t> out(params()->m);

  // F, including with the output aliasing the input.
  std::vector<uint8_t> m1 = Pattern(6, n);
  slh_dsa_f(&state, out.data(), adrs.data(), m1.data());
  const std::vector<uint8_t> f = SHAKE256Of({pk_seed, adrs, m1}, n);
  EXPECT_EQ(Bytes(out.data(), n), Bytes(f));
  slh_dsa_f(&state, m1.data(), adrs.data(), m1.data());
  EXPECT_EQ(Bytes(m1), Bytes(f));

  // H.
  const std::vector<uint8_t> m2 = Pattern(7, 2 * n);
  slh_dsa_h(&state, out.data(), adrs.data(), m2.data(), m2.data() + n);
  EXPECT_EQ(Bytes(out.data(), n), Bytes(SHAKE256Of({pk_seed, adrs, m2}, n)));

  // T_l, for the lengths that WOTS+ and FORS use, and a block boundary.
  for (size_t len : {size_t{slh_dsa_wots_len(params()) * n},
                     size_t{params()->k * n}, size_t{SHAKE256_BLOCKSIZE}}) {
    SCOPED_TRACE(len);
    const std::vector<uint8_t> ml = Pattern(8, len);
    slh_dsa_t(&state, out.data(), adrs.data(), ml.data(), ml.size());
    EXPECT_EQ(Bytes(out.data(), n), Bytes(SHAKE256Of({pk_seed, adrs, ml}, n)));
  }

  // PRF.
  slh_dsa_prf(&state, out.data(), adrs.data());
  EXPECT_EQ(Bytes(out.data(), n),
            Bytes(SHAKE256Of({pk_seed, adrs, sk_seed}, n)));

  // PRF_msg and H_msg, with and without a prefix and message.
  const std::vector<uint8_t> opt_rand = Pattern(9, n), r = Pattern(10, n);
  const std::vector<uint8_t> pre = Pattern(11, 13), msg = Pattern(12, 200);
  slh_dsa_prf_msg(&state, out.data(), opt_rand.data(), pre.data(), pre.size(),
                  msg.data(), msg.size());
  EXPECT_EQ(Bytes(out.data(), n),
            Bytes(SHAKE256Of({sk_prf, opt_rand, pre, msg}, n)));
  slh_dsa_prf_msg(&state, out.data(), opt_rand.data(), nullptr, 0, nullptr, 0);
  EXPECT_EQ(Bytes(out.data(), n), Bytes(SHAKE256Of({sk_prf, opt_rand}, n)));
  const size_t m = params()->m;
  slh_dsa_h_msg(&state, out.data(), r.data(), pre.data(), pre.size(),
                msg.data(), msg.size());
  EXPECT_EQ(Bytes(out.data(), m),
            Bytes(SHAKE256Of({r, pk_seed, pk_root, pre, msg}, m)));
  slh_dsa_h_msg(&state, out.data(), r.data(), nullptr, 0, nullptr, 0);
  EXPECT_EQ(Bytes(out.data(), m), Bytes(SHAKE256Of({r, pk_seed, pk_root}, m)));

  slh_dsa_state_cleanse(&state);
}
#endif  // !BORINGSSL_SHARED_LIBRARY

// RunACVPKeyGen checks up to |max_vectors| of the NIST ACVP key generation
// vectors.
void SLHDSATest::RunACVPKeyGen(size_t max_vectors) {
  const SLHDSA_PARAMS *params = this->params();
  size_t count = 0;
  FileTestGTest(KATPath("keyGen").c_str(), [&](FileTest *t) {
    std::string tc_id;
    std::vector<uint8_t> sk_seed, sk_prf, pk_seed, expected_pk, expected_sk;
    ASSERT_TRUE(t->GetAttribute(&tc_id, "tcId"));
    ASSERT_TRUE(t->GetBytes(&sk_seed, "sk_seed"));
    ASSERT_TRUE(t->GetBytes(&sk_prf, "sk_prf"));
    ASSERT_TRUE(t->GetBytes(&pk_seed, "pk_seed"));
    ASSERT_TRUE(t->GetBytes(&expected_pk, "pk"));
    ASSERT_TRUE(t->GetBytes(&expected_sk, "sk"));
    if (count++ >= max_vectors) {
      return;
    }

    std::vector<uint8_t> seed = sk_seed;
    seed.insert(seed.end(), sk_prf.begin(), sk_prf.end());
    seed.insert(seed.end(), pk_seed.begin(), pk_seed.end());

    std::vector<uint8_t> pk(slh_dsa_public_key_bytes(params)),
        sk(slh_dsa_private_key_bytes(params));
    ASSERT_TRUE(slh_dsa_keypair_internal(params, pk.data(), pk.size(),
                                         sk.data(), sk.size(), seed.data(),
                                         seed.size()));
    EXPECT_EQ(Bytes(pk), Bytes(expected_pk));
    EXPECT_EQ(Bytes(sk), Bytes(expected_sk));

    std::vector<uint8_t> pk_from_sk(pk.size());
    ASSERT_TRUE(slh_dsa_public_from_private(
        params, pk_from_sk.data(), pk_from_sk.size(), sk.data(), sk.size()));
    EXPECT_EQ(Bytes(pk_from_sk), Bytes(expected_pk));
  });
}

TEST_P(SLHDSATest, ACVPKeyGen) { RunACVPKeyGen(/*max_vectors=*/1); }

TEST_P(DISABLED_SLHDSASlowTest, ACVPKeyGenAll) {
  RunACVPKeyGen(/*max_vectors=*/SIZE_MAX);
}

TEST_P(SLHDSATest, ACVPSigGenVerify) { RunACVPSigGen(/*max_signs=*/0); }

TEST_P(DISABLED_SLHDSASlowTest, ACVPSigGen) { RunACVPSigGen(/*max_signs=*/1); }

TEST_P(SLHDSATest, DISABLED_ACVPSigGenAll) {
  RunACVPSigGen(/*max_signs=*/SIZE_MAX);
}

TEST_P(SLHDSATest, ACVPSigVer) {
  FileTestGTest(KATPath("sigVer").c_str(), [&](FileTest *t) {
    std::string tc_id, iface, hash, result;
    std::vector<uint8_t> pk, msg, ctx, sig;
    ASSERT_TRUE(t->GetAttribute(&tc_id, "tcId"));
    ASSERT_TRUE(t->GetAttribute(&iface, "interface"));
    ASSERT_TRUE(t->GetBytes(&pk, "pk"));
    ASSERT_TRUE(t->GetBytes(&msg, "msg"));
    if (iface != "internal") {
      ASSERT_TRUE(t->GetBytes(&ctx, "ctx"));
    }
    if (iface == "prehash") {
      ASSERT_TRUE(t->GetAttribute(&hash, "hash"));
    }
    ASSERT_TRUE(t->GetBytes(&sig, "sig"));
    ASSERT_TRUE(t->GetAttribute(&result, "result"));
    ASSERT_TRUE(result == "pass" || result == "fail");
    const int expected = result == "pass" ? 1 : 0;

    if (iface == "internal") {
      EXPECT_EQ(VerifyInternal(sig, pk, nullptr, 0, msg.data(), msg.size()),
                expected);
    } else if (iface == "pure") {
      EXPECT_EQ(
          slh_dsa_verify(params(), sig.data(), sig.size(), pk.data(), pk.size(),
                         msg.data(), msg.size(), ctx.data(), ctx.size()),
          expected);
    } else {
      ASSERT_EQ(iface, "prehash");
      // ACVP also has SHAKE128 vectors for parameter sets above category 1,
      // which are rejected.
      EXPECT_EQ(
          slh_dsa_prehash_verify(params(), sig.data(), sig.size(), pk.data(),
                                 pk.size(), PrehashNID(hash), msg.data(),
                                 msg.size(), ctx.data(), ctx.size()),
          PrehashSupported(hash) ? expected : 0);
    }
  });
}

TEST_P(DISABLED_SLHDSASlowTest, Keypair) {
  std::vector<uint8_t> pk, sk, pk2, sk2;
  ASSERT_NO_FATAL_FAILURE(GenerateKey(&pk, &sk));
  ASSERT_NO_FATAL_FAILURE(GenerateKey(&pk2, &sk2));
  EXPECT_NE(Bytes(sk), Bytes(sk2));

  // PK.seed || PK.root are the last 2n bytes of the private key.
  EXPECT_EQ(Bytes(pk), Bytes(sk.data() + 2 * n(), 2 * n()));
  std::vector<uint8_t> pk_from_sk(pk_len());
  ASSERT_TRUE(slh_dsa_public_from_private(
      params(), pk_from_sk.data(), pk_from_sk.size(), sk.data(), sk.size()));
  EXPECT_EQ(Bytes(pk_from_sk), Bytes(pk));

  // The private key is consistent, and an inconsistent one is rejected. SK.prf
  // is not bound by PK.root, so only SK.seed, PK.seed and PK.root are checked.
  EXPECT_TRUE(slh_dsa_check_private_key(params(), sk.data(), sk.size()));
  for (size_t offset : {size_t{0}, 2 * n(), 3 * n(), 4 * n() - 1}) {
    SCOPED_TRACE(offset);
    std::vector<uint8_t> bad = sk;
    bad[offset] ^= 1;
    EXPECT_FALSE(slh_dsa_check_private_key(params(), bad.data(), bad.size()));
    EXPECT_FALSE(slh_dsa_public_from_private(params(), pk_from_sk.data(),
                                             pk_from_sk.size(), bad.data(),
                                             bad.size()));
  }
  EXPECT_FALSE(slh_dsa_check_private_key(params(), sk.data(), sk.size() - 1));

  // Key generation is slh_keygen_internal on the first 3n bytes of SK.
  std::vector<uint8_t> pk3(pk_len()), sk3(sk_len());
  ASSERT_TRUE(slh_dsa_keypair_internal(params(), pk3.data(), pk3.size(),
                                       sk3.data(), sk3.size(), sk.data(),
                                       seed_len()));
  EXPECT_EQ(Bytes(pk3), Bytes(pk));
  EXPECT_EQ(Bytes(sk3), Bytes(sk));
}

TEST_P(DISABLED_SLHDSASlowTest, SignVerifyInternal) {
  if (!Is128s()) {
    GTEST_SKIP() << "Signing is slow; SLH-DSA-SHAKE-128s covers this";
  }
  std::vector<uint8_t> pk, sk;
  ASSERT_NO_FATAL_FAILURE(GenerateKey(&pk, &sk));
  static const uint8_t kMsg[] = "SLH-DSA test message";

  // Hedged signing.
  std::vector<uint8_t> addrnd(n()), sig;
  RAND_bytes(addrnd.data(), addrnd.size());
  ASSERT_TRUE(SignInternal(&sig, sk, nullptr, 0, kMsg, sizeof(kMsg), addrnd));
  EXPECT_TRUE(VerifyInternal(sig, pk, nullptr, 0, kMsg, sizeof(kMsg)));

  // The wrong message.
  EXPECT_FALSE(VerifyInternal(sig, pk, nullptr, 0, kMsg, sizeof(kMsg) - 1));

  // The wrong public key.
  std::vector<uint8_t> pk2, sk2;
  ASSERT_NO_FATAL_FAILURE(GenerateKey(&pk2, &sk2));
  EXPECT_FALSE(VerifyInternal(sig, pk2, nullptr, 0, kMsg, sizeof(kMsg)));

  // Wrong signature lengths.
  std::vector<uint8_t> short_sig(sig.begin(), sig.end() - 1);
  EXPECT_FALSE(VerifyInternal(short_sig, pk, nullptr, 0, kMsg, sizeof(kMsg)));
  std::vector<uint8_t> long_sig = sig;
  long_sig.push_back(0);
  EXPECT_FALSE(VerifyInternal(long_sig, pk, nullptr, 0, kMsg, sizeof(kMsg)));

  // Flip one bit in each part of the signature: R, the FORS signature, and
  // the first and last XMSS signatures of the hypertree.
  const size_t fors_end = n() + params()->k * (1 + params()->a) * n();
  for (size_t offset :
       {size_t{0}, n(), fors_end - 1, fors_end, sig.size() - 1}) {
    SCOPED_TRACE(offset);
    std::vector<uint8_t> bad_sig = sig;
    bad_sig[offset] ^= 1;
    EXPECT_FALSE(VerifyInternal(bad_sig, pk, nullptr, 0, kMsg, sizeof(kMsg)));
  }

  // A second hedged signature uses fresh randomness, so it differs.
  std::vector<uint8_t> sig2;
  RAND_bytes(addrnd.data(), addrnd.size());
  ASSERT_TRUE(SignInternal(&sig2, sk, nullptr, 0, kMsg, sizeof(kMsg), addrnd));
  EXPECT_NE(Bytes(sig), Bytes(sig2));
  EXPECT_TRUE(VerifyInternal(sig2, pk, nullptr, 0, kMsg, sizeof(kMsg)));
}

// The deterministic variant is the hedged variant with addrnd = PK.seed
// (FIPS 205, Section 9.2), and M = |pre| || |message| regardless of where it
// is split.
TEST_P(DISABLED_SLHDSASlowTest, DeterministicAndPrefix) {
  if (!Is128s()) {
    GTEST_SKIP() << "Signing is slow; SLH-DSA-SHAKE-128s covers this";
  }
  std::vector<uint8_t> pk, sk;
  ASSERT_NO_FATAL_FAILURE(GenerateKey(&pk, &sk));
  static const uint8_t kM[] =
      "\x00\x05"
      "contextmessage";
  const size_t m_len = sizeof(kM) - 1;

  std::vector<uint8_t> sig_det, sig_split;
  ASSERT_TRUE(SignInternal(&sig_det, sk, nullptr, 0, kM, m_len, {}));
  const std::vector<uint8_t> pk_seed(pk.begin(), pk.begin() + n());
  ASSERT_TRUE(SignInternal(&sig_split, sk, kM, 7, kM + 7, m_len - 7, pk_seed));
  EXPECT_EQ(Bytes(sig_det), Bytes(sig_split));

  for (size_t pre_len : {size_t{0}, size_t{1}, size_t{7}, m_len}) {
    SCOPED_TRACE(pre_len);
    EXPECT_TRUE(VerifyInternal(sig_det, pk, pre_len == 0 ? nullptr : kM,
                               pre_len, kM + pre_len, m_len - pre_len));
  }
}

TEST_P(SLHDSATest, PureSignVerify) {
  std::vector<uint8_t> pk, sk;
  ASSERT_NO_FATAL_FAILURE(GenerateKey(&pk, &sk));
  static const uint8_t kMsg[] = "pure SLH-DSA";
  // The longest permitted context string.
  std::vector<uint8_t> ctx(SLHDSA_MAX_CONTEXT_BYTES, 'c');

  std::vector<uint8_t> sig(sig_len());
  ASSERT_TRUE(slh_dsa_sign(params(), sig.data(), sig.size(), sk.data(),
                           sk.size(), kMsg, sizeof(kMsg), ctx.data(),
                           ctx.size()));
  EXPECT_TRUE(slh_dsa_verify(params(), sig.data(), sig.size(), pk.data(),
                             pk.size(), kMsg, sizeof(kMsg), ctx.data(),
                             ctx.size()));


  // M' = 0 || |ctx| || ctx || M (FIPS 205, Algorithm 22, line 8).
  std::vector<uint8_t> pre, m;
  ASSERT_NO_FATAL_FAILURE(
      ExternalMessage(&pre, &m, "pure", "",
                      std::vector<uint8_t>(kMsg, kMsg + sizeof(kMsg)), ctx));
  EXPECT_TRUE(
      VerifyInternal(sig, pk, pre.data(), pre.size(), m.data(), m.size()));

  // A different or missing context, the wrong message, or verification as
  // HashSLH-DSA or as the internal function all fail.
  std::vector<uint8_t> ctx2 = ctx;
  ctx2.back() ^= 1;
  EXPECT_FALSE(slh_dsa_verify(params(), sig.data(), sig.size(), pk.data(),
                              pk.size(), kMsg, sizeof(kMsg), ctx2.data(),
                              ctx2.size()));
  EXPECT_FALSE(slh_dsa_verify(params(), sig.data(), sig.size(), pk.data(),
                              pk.size(), kMsg, sizeof(kMsg), nullptr, 0));
  EXPECT_FALSE(slh_dsa_verify(params(), sig.data(), sig.size(), pk.data(),
                              pk.size(), kMsg, sizeof(kMsg) - 1, ctx.data(),
                              ctx.size()));
  for (int hash_nid : {NID_shake128, NID_shake256}) {
    EXPECT_FALSE(slh_dsa_prehash_verify(params(), sig.data(), sig.size(),
                                        pk.data(), pk.size(), hash_nid, kMsg,
                                        sizeof(kMsg), ctx.data(), ctx.size()));
  }
  EXPECT_FALSE(VerifyInternal(sig, pk, nullptr, 0, kMsg, sizeof(kMsg)));

  // Context strings are limited to 255 bytes.
  ctx.push_back('c');
  EXPECT_FALSE(slh_dsa_sign(params(), sig.data(), sig.size(), sk.data(),
                            sk.size(), kMsg, sizeof(kMsg), ctx.data(),
                            ctx.size()));
  EXPECT_FALSE(slh_dsa_verify(params(), sig.data(), sig.size(), pk.data(),
                              pk.size(), kMsg, sizeof(kMsg), ctx.data(),
                              ctx.size()));
}

// Signing is hedged, so signing twice gives different signatures.
TEST_P(DISABLED_SLHDSASlowTest, Hedged) {
  if (!Is128s()) {
    GTEST_SKIP() << "Signing is slow; SLH-DSA-SHAKE-128s covers this";
  }
  std::vector<uint8_t> pk, sk;
  ASSERT_NO_FATAL_FAILURE(GenerateKey(&pk, &sk));
  static const uint8_t kMsg[] = "hedged";
  std::vector<uint8_t> sig1(sig_len()), sig2(sig_len());
  ASSERT_TRUE(slh_dsa_sign(params(), sig1.data(), sig1.size(), sk.data(),
                           sk.size(), kMsg, sizeof(kMsg), nullptr, 0));
  ASSERT_TRUE(slh_dsa_sign(params(), sig2.data(), sig2.size(), sk.data(),
                           sk.size(), kMsg, sizeof(kMsg), nullptr, 0));
  EXPECT_NE(Bytes(sig1), Bytes(sig2));
  EXPECT_TRUE(slh_dsa_verify(params(), sig2.data(), sig2.size(), pk.data(),
                             pk.size(), kMsg, sizeof(kMsg), nullptr, 0));
}

TEST_P(DISABLED_SLHDSASlowTest, PrehashSignVerify) {
  std::vector<uint8_t> pk, sk;
  ASSERT_NO_FATAL_FAILURE(GenerateKey(&pk, &sk));
  static const uint8_t kMsg[] = "HashSLH-DSA";
  static const uint8_t kCtx[] = "context";
  const std::vector<uint8_t> msg(kMsg, kMsg + sizeof(kMsg));
  const std::vector<uint8_t> ctx(kCtx, kCtx + sizeof(kCtx));

  for (const char *hash : {"SHAKE-128", "SHAKE-256"}) {
    SCOPED_TRACE(hash);
    const int hash_nid = PrehashNID(hash);
    const int other_nid =
        hash_nid == NID_shake128 ? NID_shake256 : NID_shake128;
    std::vector<uint8_t> pre, digest;
    ASSERT_NO_FATAL_FAILURE(
        ExternalMessage(&pre, &digest, "prehash", hash, msg, ctx));
    std::vector<uint8_t> sig(sig_len());

    // SHAKE128 is only for SLH-DSA-SHAKE-128s (FIPS 205, Section 10.2.2).
    // Otherwise, every function rejects it.
    if (hash_nid == NID_shake128 && n() != 16) {
      EXPECT_EQ(slh_dsa_prehash_digest_bytes(params(), hash_nid), 0u);
      EXPECT_FALSE(slh_dsa_prehash_sign(params(), sig.data(), sig.size(),
                                        sk.data(), sk.size(), hash_nid, kMsg,
                                        sizeof(kMsg), kCtx, sizeof(kCtx)));
      EXPECT_FALSE(slh_dsa_prehash_sign_digest(
          params(), sig.data(), sig.size(), sk.data(), sk.size(), hash_nid,
          digest.data(), digest.size(), kCtx, sizeof(kCtx)));
      // |ACVPSigGen| checks that valid SHAKE128 signatures do not verify.
      continue;
    }
    EXPECT_EQ(slh_dsa_prehash_digest_bytes(params(), hash_nid), digest.size());
    if (!Is128s()) {
      continue;  // Signing is slow; SLH-DSA-SHAKE-128s covers the rest.
    }

    ASSERT_TRUE(slh_dsa_prehash_sign(params(), sig.data(), sig.size(),
                                     sk.data(), sk.size(), hash_nid, kMsg,
                                     sizeof(kMsg), kCtx, sizeof(kCtx)));
    EXPECT_TRUE(slh_dsa_prehash_verify(params(), sig.data(), sig.size(),
                                       pk.data(), pk.size(), hash_nid, kMsg,
                                       sizeof(kMsg), kCtx, sizeof(kCtx)));
    EXPECT_TRUE(slh_dsa_prehash_verify_digest(
        params(), sig.data(), sig.size(), pk.data(), pk.size(), hash_nid,
        digest.data(), digest.size(), kCtx, sizeof(kCtx)));

    // M' = 1 || |ctx| || ctx || OID || PH(M) (FIPS 205, Algorithm 23,
    // line 24).
    EXPECT_TRUE(VerifyInternal(sig, pk, pre.data(), pre.size(), digest.data(),
                               digest.size()));

    // The other pre-hash function, pure verification, a different context,
    // or the wrong message all fail.
    EXPECT_FALSE(slh_dsa_prehash_verify(params(), sig.data(), sig.size(),
                                        pk.data(), pk.size(), other_nid, kMsg,
                                        sizeof(kMsg), kCtx, sizeof(kCtx)));
    EXPECT_FALSE(slh_dsa_verify(params(), sig.data(), sig.size(), pk.data(),
                                pk.size(), kMsg, sizeof(kMsg), kCtx,
                                sizeof(kCtx)));
    EXPECT_FALSE(slh_dsa_prehash_verify(params(), sig.data(), sig.size(),
                                        pk.data(), pk.size(), hash_nid, kMsg,
                                        sizeof(kMsg), kCtx, sizeof(kCtx) - 1));
    EXPECT_FALSE(slh_dsa_prehash_verify(params(), sig.data(), sig.size(),
                                        pk.data(), pk.size(), hash_nid, kMsg,
                                        sizeof(kMsg) - 1, kCtx, sizeof(kCtx)));

    // The digest must be exactly the pre-hash function's output length.
    std::vector<uint8_t> sig2(sig_len());
    EXPECT_FALSE(slh_dsa_prehash_sign_digest(
        params(), sig2.data(), sig2.size(), sk.data(), sk.size(), hash_nid,
        digest.data(), digest.size() - 1, kCtx, sizeof(kCtx)));
    EXPECT_FALSE(slh_dsa_prehash_verify_digest(
        params(), sig.data(), sig.size(), pk.data(), pk.size(), hash_nid,
        digest.data(), digest.size() - 1, kCtx, sizeof(kCtx)));
  }

  // Signing a digest is the same as signing the message.
  std::vector<uint8_t> pre, digest;
  ASSERT_NO_FATAL_FAILURE(
      ExternalMessage(&pre, &digest, "prehash", "SHAKE-256", msg, ctx));
  std::vector<uint8_t> sig(sig_len());
  if (Is128s()) {
    ASSERT_TRUE(slh_dsa_prehash_sign_digest(
        params(), sig.data(), sig.size(), sk.data(), sk.size(), NID_shake256,
        digest.data(), digest.size(), kCtx, sizeof(kCtx)));
    EXPECT_TRUE(slh_dsa_prehash_verify(params(), sig.data(), sig.size(),
                                       pk.data(), pk.size(), NID_shake256, kMsg,
                                       sizeof(kMsg), kCtx, sizeof(kCtx)));
  }

  // Other hash functions are not supported.
  EXPECT_EQ(slh_dsa_prehash_digest_bytes(params(), NID_sha256), 0u);
  EXPECT_EQ(slh_dsa_prehash_digest_bytes(nullptr, NID_shake256), 0u);
  EXPECT_FALSE(slh_dsa_prehash_sign(params(), sig.data(), sig.size(), sk.data(),
                                    sk.size(), NID_sha256, kMsg, sizeof(kMsg),
                                    kCtx, sizeof(kCtx)));
  EXPECT_FALSE(slh_dsa_prehash_verify(params(), sig.data(), sig.size(),
                                      pk.data(), pk.size(), NID_sha256, kMsg,
                                      sizeof(kMsg), kCtx, sizeof(kCtx)));
}

TEST_P(DISABLED_SLHDSASlowTest, InvalidArguments) {
  if (!Is128s()) {
    GTEST_SKIP() << "Signing is slow; SLH-DSA-SHAKE-128s covers this";
  }
  std::vector<uint8_t> pk(pk_len()), sk(sk_len()), seed(seed_len());
  std::vector<uint8_t> sig(sig_len()), addrnd(n() + 1);
  static const uint8_t kMsg[] = "msg";

  // Key generation.
  EXPECT_FALSE(
      slh_dsa_keypair(nullptr, pk.data(), pk.size(), sk.data(), sk.size()));
  EXPECT_FALSE(slh_dsa_keypair(params(), pk.data(), pk.size() - 1, sk.data(),
                               sk.size()));
  EXPECT_FALSE(slh_dsa_keypair(params(), pk.data(), pk.size(), sk.data(),
                               sk.size() + 1));
  EXPECT_FALSE(slh_dsa_keypair_internal(nullptr, pk.data(), pk.size(),
                                        sk.data(), sk.size(), seed.data(),
                                        seed.size()));
  EXPECT_FALSE(slh_dsa_keypair_internal(params(), nullptr, pk.size(), sk.data(),
                                        sk.size(), seed.data(), seed.size()));
  EXPECT_FALSE(slh_dsa_keypair_internal(params(), pk.data(), pk.size(), nullptr,
                                        sk.size(), seed.data(), seed.size()));
  EXPECT_FALSE(slh_dsa_keypair_internal(params(), pk.data(), pk.size(),
                                        sk.data(), sk.size(), nullptr,
                                        seed.size()));
  EXPECT_FALSE(slh_dsa_keypair_internal(params(), pk.data(), pk.size() - 1,
                                        sk.data(), sk.size(), seed.data(),
                                        seed.size()));
  EXPECT_FALSE(slh_dsa_keypair_internal(params(), pk.data(), pk.size(),
                                        sk.data(), sk.size() + 1, seed.data(),
                                        seed.size()));
  EXPECT_FALSE(slh_dsa_keypair_internal(params(), pk.data(), pk.size(),
                                        sk.data(), sk.size(), seed.data(),
                                        seed.size() - 1));
  ASSERT_TRUE(slh_dsa_keypair_internal(params(), pk.data(), pk.size(),
                                       sk.data(), sk.size(), seed.data(),
                                       seed.size()));

  // Signing. None of these reach the signing code, so they are cheap.
  auto sign = [&](const SLHDSA_PARAMS *p, uint8_t *out, size_t out_len,
                  const uint8_t *key, size_t key_len, const uint8_t *pre,
                  size_t pre_len, const uint8_t *msg, size_t msg_len,
                  const uint8_t *rnd, size_t rnd_len) {
    return slh_dsa_sign_internal(p, out, out_len, key, key_len, pre, pre_len,
                                 msg, msg_len, rnd, rnd_len);
  };
  const uint8_t *s = sk.data();
  EXPECT_FALSE(sign(nullptr, sig.data(), sig.size(), s, sk.size(), nullptr, 0,
                    kMsg, sizeof(kMsg), nullptr, 0));
  EXPECT_FALSE(sign(params(), nullptr, sig.size(), s, sk.size(), nullptr, 0,
                    kMsg, sizeof(kMsg), nullptr, 0));
  EXPECT_FALSE(sign(params(), sig.data(), sig.size(), nullptr, sk.size(),
                    nullptr, 0, kMsg, sizeof(kMsg), nullptr, 0));
  EXPECT_FALSE(sign(params(), sig.data(), sig.size() - 1, s, sk.size(), nullptr,
                    0, kMsg, sizeof(kMsg), nullptr, 0));
  EXPECT_FALSE(sign(params(), sig.data(), sig.size(), s, sk.size() - 1, nullptr,
                    0, kMsg, sizeof(kMsg), nullptr, 0));
  EXPECT_FALSE(sign(params(), sig.data(), sig.size(), s, sk.size(), nullptr, 1,
                    kMsg, sizeof(kMsg), nullptr, 0));
  EXPECT_FALSE(sign(params(), sig.data(), sig.size(), s, sk.size(), nullptr, 0,
                    nullptr, 1, nullptr, 0));
  // addrnd must be exactly n bytes, and absent for deterministic signing.
  EXPECT_FALSE(sign(params(), sig.data(), sig.size(), s, sk.size(), nullptr, 0,
                    kMsg, sizeof(kMsg), addrnd.data(), n() - 1));
  EXPECT_FALSE(sign(params(), sig.data(), sig.size(), s, sk.size(), nullptr, 0,
                    kMsg, sizeof(kMsg), addrnd.data(), n() + 1));
  EXPECT_FALSE(sign(params(), sig.data(), sig.size(), s, sk.size(), nullptr, 0,
                    kMsg, sizeof(kMsg), addrnd.data(), 0));
  EXPECT_FALSE(sign(params(), sig.data(), sig.size(), s, sk.size(), nullptr, 0,
                    kMsg, sizeof(kMsg), nullptr, n()));
  EXPECT_FALSE(slh_dsa_sign(nullptr, sig.data(), sig.size(), s, sk.size(), kMsg,
                            sizeof(kMsg), nullptr, 0));
  EXPECT_FALSE(slh_dsa_sign(params(), sig.data(), sig.size(), s, sk.size(),
                            kMsg, sizeof(kMsg), nullptr, 1));
  EXPECT_FALSE(slh_dsa_prehash_sign(params(), sig.data(), sig.size(), s,
                                    sk.size(), NID_shake256, nullptr, 1,
                                    nullptr, 0));
  EXPECT_FALSE(slh_dsa_prehash_sign_digest(params(), sig.data(), sig.size(), s,
                                           sk.size(), NID_shake256, nullptr, 64,
                                           nullptr, 0));

  // An empty message is valid.
  ASSERT_TRUE(SignInternal(&sig, sk, nullptr, 0, nullptr, 0, {}));
  EXPECT_TRUE(VerifyInternal(sig, pk, nullptr, 0, nullptr, 0));

  // Verification.
  EXPECT_FALSE(slh_dsa_verify_internal(nullptr, sig.data(), sig.size(),
                                       pk.data(), pk.size(), nullptr, 0,
                                       nullptr, 0));
  EXPECT_FALSE(slh_dsa_verify_internal(params(), nullptr, sig.size(), pk.data(),
                                       pk.size(), nullptr, 0, nullptr, 0));
  EXPECT_FALSE(slh_dsa_verify_internal(params(), sig.data(), sig.size(),
                                       nullptr, pk.size(), nullptr, 0, nullptr,
                                       0));
  EXPECT_FALSE(slh_dsa_verify_internal(params(), sig.data(), sig.size(),
                                       pk.data(), pk.size() - 1, nullptr, 0,
                                       nullptr, 0));
  EXPECT_FALSE(slh_dsa_verify_internal(params(), sig.data(), sig.size(),
                                       pk.data(), pk.size(), nullptr, 1,
                                       nullptr, 0));
  EXPECT_FALSE(slh_dsa_verify_internal(params(), sig.data(), sig.size(),
                                       pk.data(), pk.size(), nullptr, 0,
                                       nullptr, 1));
  EXPECT_FALSE(slh_dsa_verify(nullptr, sig.data(), sig.size(), pk.data(),
                              pk.size(), nullptr, 0, nullptr, 0));
  EXPECT_FALSE(slh_dsa_prehash_verify(params(), sig.data(), sig.size(),
                                      pk.data(), pk.size(), NID_shake256,
                                      nullptr, 1, nullptr, 0));

  // Public key extraction.
  std::vector<uint8_t> pk2(pk_len());
  EXPECT_FALSE(slh_dsa_public_from_private(nullptr, pk2.data(), pk2.size(),
                                           sk.data(), sk.size()));
  EXPECT_FALSE(slh_dsa_public_from_private(params(), nullptr, pk2.size(),
                                           sk.data(), sk.size()));
  EXPECT_FALSE(slh_dsa_public_from_private(params(), pk2.data(), pk2.size(),
                                           nullptr, sk.size()));
  EXPECT_FALSE(slh_dsa_public_from_private(params(), pk2.data(), pk2.size() + 1,
                                           sk.data(), sk.size()));
  EXPECT_FALSE(slh_dsa_public_from_private(params(), pk2.data(), pk2.size(),
                                           sk.data(), sk.size() - 1));
}

#if (defined(__linux__) || defined(__APPLE__)) && defined(__GNUC__) && \
    !defined(OPENSSL_ASAN) && !defined(OPENSSL_HWASAN) &&              \
    !defined(OPENSSL_MSAN) && !defined(OPENSSL_TSAN) &&                \
    !defined(__SANITIZE_ADDRESS__) && !defined(__SANITIZE_THREAD__)
// Stack painting for |StackScrub|. The test calls |PaintStack|, an operation
// and |CountBytes| from the same frame, so all three start at the same stack
// pointer, and |kStackRegion| bytes below it are what the operation could use.
// The buffers must stay uninitialized, even with -ftrivial-auto-var-init.
#if defined(__has_attribute)
#if __has_attribute(uninitialized)
#define SLHDSA_TEST_UNINITIALIZED __attribute__((uninitialized))
#endif
#endif
#if !defined(SLHDSA_TEST_UNINITIALIZED)
#define SLHDSA_TEST_UNINITIALIZED
#endif
constexpr size_t kStackRegion = 64 * 1024;
constexpr uint8_t kStackPaint = 0xa5;

OPENSSL_NOINLINE void FillWithPaint(volatile uint8_t *buf) {
  for (size_t i = 0; i < kStackRegion; i++) {
    buf[i] = kStackPaint;
  }
}

// PaintStack fills |kStackRegion| bytes below the caller's frame with
// |kStackPaint|.
OPENSSL_NOINLINE void PaintStack() {
  volatile uint8_t buf[kStackRegion] SLHDSA_TEST_UNINITIALIZED;
  FillWithPaint(buf);
}

OPENSSL_NOINLINE size_t CountBytesIn(volatile uint8_t *buf, size_t lo,
                                     size_t hi, bool allow_paint) {
  size_t count = 0;
  for (size_t depth = lo; depth < hi; depth++) {
    const uint8_t b = buf[kStackRegion - depth];
    if (b != 0 && (!allow_paint || b != kStackPaint)) {
      count++;
    }
  }
  return count;
}

// CountBytes returns the number of bytes at depths [lo, hi) below the caller's
// frame that are not zero, or, if |allow_paint| is true, neither zero nor
// |kStackPaint|.
OPENSSL_NOINLINE size_t CountBytes(size_t lo, size_t hi, bool allow_paint) {
  volatile uint8_t buf[kStackRegion] SLHDSA_TEST_UNINITIALIZED;
  return CountBytesIn(buf, lo, hi, allow_paint);
}

// Every exported operation overwrites the stack it used before returning
// (FIPS 205, Section 3.1). After each operation, the stack from just below the
// operation's own frame to the end of the scrub must be zero. Below that,
// apart from the few bytes of the scrub's own call to |OPENSSL_cleanse|, there
// must be nothing but zeros and paint, so the operation left nothing in stack
// that the scrub does not cover. Without the scrub, an operation leaves
// thousands of bytes. This reads stale stack memory, so it is
// disabled by default and runs natively from util/all_tests.json, on Linux and
// macOS only.
TEST_P(SLHDSATest, DISABLED_StackScrub) {
  if (!Is128s()) {
    GTEST_SKIP() << "One parameter set is enough";
  }
  std::vector<uint8_t> pk(pk_len()), sk(sk_len()), sig(sig_len());
  std::vector<uint8_t> seed(seed_len(), 1), addrnd(n(), 2);
  static const uint8_t kMsg[] = "stack";
  // The scrub is SLHDSA_STACK_SCRUB_BYTES, 16 KB, below the operation's own
  // frame, which is well under 1 KB.
  constexpr size_t kZeroLo = 1024, kZeroHi = 15 * 1024, kEnd = 60 * 1024;
  // Enough for the frames of two nested scrubs' calls to |OPENSSL_cleanse|,
  // even unoptimized.
  constexpr size_t kMaxScrubFrames = 256;

  const std::vector<std::pair<const char *, std::function<bool()>>> ops = {
      {"slh_dsa_keypair",
       [&] {
         return slh_dsa_keypair(params(), pk.data(), pk.size(), sk.data(),
                                sk.size());
       }},
      {"slh_dsa_keypair_internal",
       [&] {
         return slh_dsa_keypair_internal(params(), pk.data(), pk.size(),
                                         sk.data(), sk.size(), seed.data(),
                                         seed.size());
       }},
      {"slh_dsa_check_private_key",
       [&] {
         return slh_dsa_check_private_key(params(), sk.data(), sk.size());
       }},
      {"slh_dsa_sign",
       [&] {
         return slh_dsa_sign(params(), sig.data(), sig.size(), sk.data(),
                             sk.size(), kMsg, sizeof(kMsg), nullptr, 0);
       }},
      {"slh_dsa_verify",
       [&] {
         return slh_dsa_verify(params(), sig.data(), sig.size(), pk.data(),
                               pk.size(), kMsg, sizeof(kMsg), nullptr, 0);
       }},
      {"slh_dsa_prehash_sign",
       [&] {
         return slh_dsa_prehash_sign(params(), sig.data(), sig.size(),
                                     sk.data(), sk.size(), NID_shake128, kMsg,
                                     sizeof(kMsg), nullptr, 0);
       }},
      {"slh_dsa_prehash_verify",
       [&] {
         return slh_dsa_prehash_verify(params(), sig.data(), sig.size(),
                                       pk.data(), pk.size(), NID_shake128, kMsg,
                                       sizeof(kMsg), nullptr, 0);
       }},
      {"slh_dsa_sign_internal",
       [&] {
         return slh_dsa_sign_internal(
             params(), sig.data(), sig.size(), sk.data(), sk.size(), nullptr, 0,
             kMsg, sizeof(kMsg), addrnd.data(), addrnd.size());
       }},
      {"slh_dsa_verify_internal",
       [&] {
         return slh_dsa_verify_internal(params(), sig.data(), sig.size(),
                                        pk.data(), pk.size(), nullptr, 0, kMsg,
                                        sizeof(kMsg));
       }},
  };

  // Run each operation once first, so that one-time work, such as seeding the
  // RBG or resolving symbols, doesn't count.
  for (const auto &op : ops) {
    ASSERT_TRUE(op.second()) << op.first;
  }
  for (const auto &op : ops) {
    PaintStack();
    ASSERT_TRUE(op.second()) << op.first;
    EXPECT_EQ(CountBytes(kZeroLo, kZeroHi, /*allow_paint=*/false), 0u)
        << op.first;
    EXPECT_LE(CountBytes(kZeroHi, kEnd, /*allow_paint=*/true), kMaxScrubFrames)
        << op.first;
  }
}
#endif

#if defined(AWSLC_FIPS)
// SLH-DSA has no self-tests yet, so it must not be reported as an approved
// service, even though its SHAKE256 and RBG calls are.
TEST_P(DISABLED_SLHDSASlowTest, NotApproved) {
  if (!Is128s()) {
    GTEST_SKIP() << "Signing is slow; SLH-DSA-SHAKE-128s covers this";
  }
  std::vector<uint8_t> pk(pk_len()), sk(sk_len()), sig(sig_len());
  static const uint8_t kMsg[] = "msg";
  FIPSStatus approved = AWSLC_APPROVED;

  CALL_SERVICE_AND_CHECK_APPROVED(
      approved, ASSERT_TRUE(slh_dsa_keypair(params(), pk.data(), pk.size(),
                                            sk.data(), sk.size())));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);

  CALL_SERVICE_AND_CHECK_APPROVED(
      approved,
      ASSERT_TRUE(slh_dsa_sign(params(), sig.data(), sig.size(), sk.data(),
                               sk.size(), kMsg, sizeof(kMsg), nullptr, 0)));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(
      approved,
      ASSERT_TRUE(slh_dsa_verify(params(), sig.data(), sig.size(), pk.data(),
                                 pk.size(), kMsg, sizeof(kMsg), nullptr, 0)));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);

  // SHAKE128 is only for SLH-DSA-SHAKE-128s.
  const int hash_nid = n() == 16 ? NID_shake128 : NID_shake256;
  CALL_SERVICE_AND_CHECK_APPROVED(
      approved, ASSERT_TRUE(slh_dsa_prehash_sign(
                    params(), sig.data(), sig.size(), sk.data(), sk.size(),
                    hash_nid, kMsg, sizeof(kMsg), nullptr, 0)));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(
      approved, ASSERT_TRUE(slh_dsa_prehash_verify(
                    params(), sig.data(), sig.size(), pk.data(), pk.size(),
                    hash_nid, kMsg, sizeof(kMsg), nullptr, 0)));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);

  CALL_SERVICE_AND_CHECK_APPROVED(
      approved,
      ASSERT_TRUE(VerifyInternal(sig, pk, nullptr, 0, nullptr, 0) == 0));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);

  // The rest of the module's services, including the internal functions.
  std::vector<uint8_t> digest(slh_dsa_prehash_digest_bytes(params(), hash_nid));
  CALL_SERVICE_AND_CHECK_APPROVED(
      approved, ASSERT_TRUE(slh_dsa_prehash_sign_digest(
                    params(), sig.data(), sig.size(), sk.data(), sk.size(),
                    hash_nid, digest.data(), digest.size(), nullptr, 0)));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(
      approved, ASSERT_TRUE(slh_dsa_prehash_verify_digest(
                    params(), sig.data(), sig.size(), pk.data(), pk.size(),
                    hash_nid, digest.data(), digest.size(), nullptr, 0)));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(
      approved,
      ASSERT_TRUE(slh_dsa_check_private_key(params(), sk.data(), sk.size())));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);
  std::vector<uint8_t> seed(seed_len(), 1);
  CALL_SERVICE_AND_CHECK_APPROVED(
      approved, ASSERT_TRUE(slh_dsa_keypair_internal(
                    params(), pk.data(), pk.size(), sk.data(), sk.size(),
                    seed.data(), seed.size())));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);
  CALL_SERVICE_AND_CHECK_APPROVED(
      approved,
      ASSERT_TRUE(SignInternal(&sig, sk, nullptr, 0, kMsg, sizeof(kMsg), {})));
  EXPECT_EQ(approved, AWSLC_NOT_APPROVED);
}
#endif

}  // namespace
