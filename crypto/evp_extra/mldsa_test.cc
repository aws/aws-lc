#include <gtest/gtest.h>
#include <openssl/evp.h>
#include <openssl/obj.h>
#include <cstddef>
#include <functional>

// Need ML-DSA internal headers to manipulate and validate the private key
extern "C" {
#include "../fipsmodule/ml_dsa/ml_dsa_ref/packing.h"
#include "../fipsmodule/ml_dsa/ml_dsa_ref/params.h"
#include "../fipsmodule/ml_dsa/ml_dsa_ref/polyvec.h"
}

// ML-DSA parameter sets
// https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#section.4
struct MLDSAParamSet {
  const char name[20];
  const int nid;
};

static const struct MLDSAParamSet kMLDSAs[] = {{"MLDSA44", NID_MLDSA44},
                                               {"MLDSA65", NID_MLDSA65},
                                               {"MLDSA87", NID_MLDSA87}};

class MLDSATest : public testing::TestWithParam<MLDSAParamSet> {
 protected:
  // Corruption function type: takes unpacked key components and corrupts them
  using CorruptionFn =
      std::function<void(polyvecl *s1, polyveck *s2, polyveck *t0)>;

  // Helper to test a corrupted key: unpack, corrupt, repack, and test signing
  static void TestCorruptedKey(const MLDSAParamSet &kMLDSA,
                               ml_dsa_params *params,
                               const uint8_t *honest_key_bytes,
                               CorruptionFn corrupt,
                               const char *component_name) {
    polyvecl s1;
    polyveck s2, t0;
    uint8_t rho[ML_DSA_SEEDBYTES], tr[ML_DSA_TRBYTES], key[ML_DSA_SEEDBYTES];

    // Unpack the honest key
    ml_dsa_unpack_sk(params, rho, tr, key, &t0, &s1, &s2, honest_key_bytes);

    // Apply the corruption
    corrupt(&s1, &s2, &t0);

    // Repack the corrupted key
    std::vector<uint8_t> corrupted_key(params->secret_key_bytes);
    ml_dsa_pack_sk(params, corrupted_key.data(), rho, tr, key, &t0, &s1, &s2);

    // Verify the corrupted key differs from the honest key
    EXPECT_NE(std::memcmp(corrupted_key.data(), honest_key_bytes,
                          params->secret_key_bytes),
              0)
        << "Corrupted " << component_name << " should differ from honest key";

    // Try to import the corrupted key
    bssl::UniquePtr<EVP_PKEY> corrupted_pkey(EVP_PKEY_pqdsa_new_raw_private_key(
        kMLDSA.nid, corrupted_key.data(), corrupted_key.size()));

    EXPECT_FALSE(corrupted_pkey.get())
        << "Imported " << kMLDSA.name << " key with corrupted "
        << component_name << " and inconsistent components";

    // Let's try to make a better corrupted key by making it consistent
    std::vector<uint8_t> better_corrupted_key = corrupted_key;
    // recompute the public key
    std::vector<uint8_t> new_pk(params->public_key_bytes);
    ml_dsa_pack_pk_from_sk(params, new_pk.data(), better_corrupted_key.data());
    // recompute tr = SHAKE256(pk, 64)
    std::vector<uint8_t> new_tr(ML_DSA_TRBYTES);
    bssl::ScopedEVP_MD_CTX md_ctx;
    ASSERT_TRUE(EVP_DigestInit_ex(md_ctx.get(), EVP_shake256(), nullptr));
    ASSERT_TRUE(EVP_DigestUpdate(md_ctx.get(), new_pk.data(),
                                 params->public_key_bytes));
    ASSERT_TRUE(EVP_DigestFinalXOF(md_ctx.get(), new_tr.data(), new_tr.size()));

    // Repack the corrupted key
    ml_dsa_pack_sk(params, better_corrupted_key.data(), rho, new_tr.data(),
                   new_pk.data(), &t0, &s1, &s2);
    EXPECT_NE(std::memcmp(better_corrupted_key.data(), corrupted_key.data(),
                          params->secret_key_bytes),
              0)
        << "Better corrupted key should differ from the simple corrupted key";

    // Try to import the corrupted key
    bssl::UniquePtr<EVP_PKEY> better_corrupted_pkey(
        EVP_PKEY_pqdsa_new_raw_private_key(kMLDSA.nid, corrupted_key.data(),
                                           corrupted_key.size()));

    EXPECT_FALSE(better_corrupted_pkey.get())
        << "Imported " << kMLDSA.name << " key with corrupted "
        << component_name;

    // If the better corrupted key was incorrectly imported, lets see what
    // happens when it is used to sign and verify.
    if (better_corrupted_pkey) {
      bssl::UniquePtr<EVP_MD_CTX> md_ctx(EVP_MD_CTX_new());
      ASSERT_TRUE(md_ctx);

      std::vector<uint8_t> msg = std::vector<uint8_t>(32, 0x42);

      std::vector<uint8_t> sig = std::vector<uint8_t>(params->bytes);
      size_t sig_len = sig.size();

      int sign_result =
          EVP_DigestSignInit(md_ctx.get(), nullptr, nullptr, nullptr,
                             better_corrupted_pkey.get()) &&
          EVP_DigestSign(md_ctx.get(), sig.data(), &sig_len, msg.data(),
                         msg.size());
      EXPECT_TRUE(sign_result) << "Signing suceeded using " << kMLDSA.name
                               << " key with corrupted " << component_name;
      EXPECT_FALSE(sign_result) << "Signing failed using " << kMLDSA.name
                                << " key with corrupted " << component_name;

      bssl::ScopedEVP_MD_CTX verify_ctx;
      int verify_result =
          EVP_DigestVerifyInit(verify_ctx.get(), nullptr, nullptr, nullptr,
                               better_corrupted_pkey.get()) &&
          EVP_DigestVerify(verify_ctx.get(), sig.data(), sig_len, msg.data(),
                           msg.size());

      EXPECT_TRUE(verify_result)
          << "Verification suceeded using " << kMLDSA.name
          << " key with corrupted " << component_name;
      EXPECT_FALSE(verify_result)
          << "Verification suceeded using " << kMLDSA.name
          << " key with corrupted " << component_name;
    }
  }
};

INSTANTIATE_TEST_SUITE_P(All, MLDSATest, testing::ValuesIn(kMLDSAs),
                         [](const testing::TestParamInfo<MLDSAParamSet> &params)
                             -> std::string { return params.param.name; });

TEST_P(MLDSATest, ExpandedKeyValidation) {
  const MLDSAParamSet ps = GetParam();

  // This goal of this test is to verify that we reject invalid extended keys,
  // because they can cause undefined behavior including producing unverifiable
  // signatures.

  ml_dsa_params params;
  if (ps.nid == NID_MLDSA44) {
    ml_dsa_44_params_init(&params);
  } else if (ps.nid == NID_MLDSA65) {
    ml_dsa_65_params_init(&params);
  } else if (ps.nid == NID_MLDSA87) {
    ml_dsa_87_params_init(&params);
  } else {
    FAIL() << "Unexpected NID!";
  }

  // Let's start by generating a honest private key from a fixed seed
  std::vector<uint8_t> seed = std::vector<uint8_t>(32, 0x42);
  bssl::UniquePtr<EVP_PKEY> honest_pkey(
      EVP_PKEY_pqdsa_new_raw_private_key(ps.nid, seed.data(), seed.size()));
  ASSERT_TRUE(honest_pkey.get());

  // Now, let's export the private key to bytes
  size_t key_len = params.secret_key_bytes;
  std::vector<uint8_t> key_bytes(key_len);
  ASSERT_TRUE(EVP_PKEY_get_raw_private_key(honest_pkey.get(), key_bytes.data(),
                                           &key_len));

  for (auto i = 0; i < params.l; i++) {
    for (auto j :
         {0 /* first coeff */, 127, 255 /* last coeff */, 95, 42, 224}) {
      // Test 1: Corrupt s1
      TestCorruptedKey(
          ps, &params, key_bytes.data(),
          [&params, i, j](polyvecl *s1, polyveck *, polyveck *) {
            s1->vec[i].coeffs[j] = params.eta + 1;
          },
          "s1");
      TestCorruptedKey(
          ps, &params, key_bytes.data(),
          [&params, i, j](polyvecl *s1, polyveck *, polyveck *) {
            s1->vec[i].coeffs[j] = -(params.eta + 1);
          },
          "s1");


      // Test 2: Corrupt s2
      TestCorruptedKey(
          ps, &params, key_bytes.data(),
          [&params, i, j](polyvecl *, polyveck *s2, polyveck *) {
            s2->vec[i].coeffs[j] = params.eta + 1;
          },
          "s2");
      TestCorruptedKey(
          ps, &params, key_bytes.data(),
          [&params, i, j](polyvecl *, polyveck *s2, polyveck *) {
            s2->vec[i].coeffs[j] = -(params.eta + 1);
          },
          "s2");
    }
  }
}
