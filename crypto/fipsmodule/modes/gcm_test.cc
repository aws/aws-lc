// Copyright (c) 2008 The OpenSSL Project.  All rights reserved.
// SPDX-License-Identifier: Apache-2.0

#include <stdio.h>
#include <string.h>

#include <vector>

#include <gtest/gtest.h>

#include <openssl/aes.h>

#include "../../internal.h"
#include "../../test/abi_test.h"
#include "../../test/file_test.h"
#include "../../test/test_util.h"
#include "../aes/internal.h"
#include "../cipher/internal.h"
#include "../cpucap/internal.h"
#include "internal.h"


TEST(GCMTest, TestVectors) {
  FileTestGTest("crypto/fipsmodule/modes/gcm_tests.txt", [](FileTest *t) {
    std::vector<uint8_t> key, plaintext, additional_data, nonce, ciphertext,
        tag;
    ASSERT_TRUE(t->GetBytes(&key, "Key"));
    ASSERT_TRUE(t->GetBytes(&plaintext, "Plaintext"));
    ASSERT_TRUE(t->GetBytes(&additional_data, "AdditionalData"));
    ASSERT_TRUE(t->GetBytes(&nonce, "Nonce"));
    ASSERT_TRUE(t->GetBytes(&ciphertext, "Ciphertext"));
    ASSERT_TRUE(t->GetBytes(&tag, "Tag"));

    ASSERT_EQ(plaintext.size(), ciphertext.size());
    ASSERT_TRUE(key.size() == 16 || key.size() == 24 || key.size() == 32);
    ASSERT_EQ(16u, tag.size());

    std::vector<uint8_t> out(plaintext.size());
    AES_KEY aes_key;
    ASSERT_EQ(0, AES_set_encrypt_key(key.data(), key.size() * 8, &aes_key));

    GCM128_CONTEXT ctx;
    OPENSSL_memset(&ctx, 0, sizeof(ctx));
    CRYPTO_gcm128_init_key(&ctx.gcm_key, &aes_key, AES_encrypt, 0);
    CRYPTO_gcm128_setiv(&ctx, &aes_key, nonce.data(), nonce.size());
    if (!additional_data.empty()) {
      CRYPTO_gcm128_aad(&ctx, additional_data.data(), additional_data.size());
    }
    if (!plaintext.empty()) {
      CRYPTO_gcm128_encrypt(&ctx, &aes_key, plaintext.data(), out.data(),
                            plaintext.size());
    }

    std::vector<uint8_t> got_tag(tag.size());
    CRYPTO_gcm128_tag(&ctx, got_tag.data(), got_tag.size());
    EXPECT_EQ(Bytes(tag), Bytes(got_tag));
    EXPECT_EQ(Bytes(ciphertext), Bytes(out));

    CRYPTO_gcm128_setiv(&ctx, &aes_key, nonce.data(), nonce.size());
    OPENSSL_memset(out.data(), 0, out.size());
    if (!additional_data.empty()) {
      CRYPTO_gcm128_aad(&ctx, additional_data.data(), additional_data.size());
    }
    if (!ciphertext.empty()) {
      CRYPTO_gcm128_decrypt(&ctx, &aes_key, ciphertext.data(), out.data(),
                            ciphertext.size());
    }
    ASSERT_TRUE(CRYPTO_gcm128_finish(&ctx, tag.data(), tag.size()));
    EXPECT_EQ(Bytes(plaintext), Bytes(out));
  });
}

// |aes_ctr_set_key| is not exported from a shared libcrypto.
#if !defined(BORINGSSL_SHARED_LIBRARY)
// AES-GCM seal and open do not zero |GCM128_CONTEXT| before
// |CRYPTO_gcm128_setiv|. Check that this is safe: a context filled with 0x56
// must behave exactly like a zeroed one.
TEST(GCMTest, ContextNeedsNoZeroing) {
  static const uint8_t kKey[32] = {
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
      0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
      0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f};
  static const uint8_t kIV[16] = {0xca, 0xfe, 0xba, 0xbe, 0xfa, 0xce,
                                  0xdb, 0xad, 0xde, 0xca, 0xf8, 0x88,
                                  0x01, 0x02, 0x03, 0x04};
  uint8_t aad[16] = {0}, in[100] = {0}, zeroed_ct[sizeof(in)] = {0},
          poisoned_ct[sizeof(in)] = {0}, zeroed_pt[sizeof(in)] = {0},
          poisoned_pt[sizeof(in)] = {0}, zeroed_tag[16] = {0},
          poisoned_tag[16] = {0}, zeroed_dec_tag[16] = {0},
          poisoned_dec_tag[16] = {0};
  AES_KEY aes_key;
  GCM128_KEY gcm_key;
  GCM128_CONTEXT zeroed, poisoned;
  OPENSSL_memset(&aes_key, 0, sizeof(aes_key));
  OPENSSL_memset(&gcm_key, 0, sizeof(gcm_key));

  for (size_t i = 0; i < sizeof(aad); i++) {
    aad[i] = (uint8_t)(0x80 + i);
  }
  for (size_t i = 0; i < sizeof(in); i++) {
    in[i] = (uint8_t)i;
  }

  for (size_t key_len : {16, 24, 32}) {
    // A 12-byte IV is used directly; other lengths are hashed with GHASH.
    for (size_t iv_len : {12, 16}) {
      SCOPED_TRACE(key_len);
      SCOPED_TRACE(iv_len);

      // Set up the key as AES-GCM seal and open do.
      ctr128_f ctr = aes_ctr_set_key(&aes_key, &gcm_key, NULL, kKey, key_len);
      if (ctr == NULL) {
        // Only 32-bit x86 using vpaes (no AES-NI) has no CTR-mode function.
        GTEST_SKIP() << "No CTR-mode AES function on this CPU";
      }

      // Encryption. Set up both contexts as AES-GCM seal does.
      OPENSSL_memset(&zeroed, 0, sizeof(zeroed));
      OPENSSL_memset(&poisoned, 0x56, sizeof(poisoned));
      OPENSSL_memcpy(&zeroed.gcm_key, &gcm_key, sizeof(gcm_key));
      OPENSSL_memcpy(&poisoned.gcm_key, &gcm_key, sizeof(gcm_key));

      CRYPTO_gcm128_setiv(&zeroed, &aes_key, kIV, iv_len);
      CRYPTO_gcm128_setiv(&poisoned, &aes_key, kIV, iv_len);

      EXPECT_EQ(Bytes(zeroed.Yi, sizeof(zeroed.Yi)),
                Bytes(poisoned.Yi, sizeof(poisoned.Yi)));
      EXPECT_EQ(Bytes(zeroed.EK0, sizeof(zeroed.EK0)),
                Bytes(poisoned.EK0, sizeof(poisoned.EK0)));
      EXPECT_EQ(Bytes(zeroed.Xi, sizeof(zeroed.Xi)),
                Bytes(poisoned.Xi, sizeof(poisoned.Xi)));
      ASSERT_EQ(0u, poisoned.len.aad);
      ASSERT_EQ(0u, poisoned.len.msg);
      ASSERT_EQ(0u, poisoned.mres);
      ASSERT_EQ(0u, poisoned.ares);

      // Pass the AAD in two calls, split mid-block, so that the second call
      // continues the partial block recorded in |ares|.
      ASSERT_TRUE(CRYPTO_gcm128_aad(&zeroed, aad, 5));
      ASSERT_TRUE(CRYPTO_gcm128_aad(&zeroed, aad + 5, sizeof(aad) - 5));

      // Encrypt the first 7 bytes. This leaves a partial block, with the
      // unused keystream in |EKi|.
      ASSERT_TRUE(CRYPTO_gcm128_encrypt_ctr32(&zeroed, &aes_key, in, zeroed_ct,
                                              7, ctr));
      // Encrypt the remaining bytes, starting with the rest of that block,
      // which reads |EKi|.
      ASSERT_TRUE(CRYPTO_gcm128_encrypt_ctr32(
          &zeroed, &aes_key, in + 7, zeroed_ct + 7, sizeof(in) - 7, ctr));
      CRYPTO_gcm128_tag(&zeroed, zeroed_tag, sizeof(zeroed_tag));

      // The same steps with the 0x56 context must give the same result.
      ASSERT_TRUE(CRYPTO_gcm128_aad(&poisoned, aad, 5));
      ASSERT_TRUE(CRYPTO_gcm128_aad(&poisoned, aad + 5, sizeof(aad) - 5));
      ASSERT_TRUE(CRYPTO_gcm128_encrypt_ctr32(&poisoned, &aes_key, in,
                                              poisoned_ct, 7, ctr));
      ASSERT_TRUE(CRYPTO_gcm128_encrypt_ctr32(
          &poisoned, &aes_key, in + 7, poisoned_ct + 7, sizeof(in) - 7, ctr));
      CRYPTO_gcm128_tag(&poisoned, poisoned_tag, sizeof(poisoned_tag));

      EXPECT_EQ(Bytes(zeroed_ct, sizeof(zeroed_ct)),
                Bytes(poisoned_ct, sizeof(poisoned_ct)));
      EXPECT_EQ(Bytes(zeroed_tag, sizeof(zeroed_tag)),
                Bytes(poisoned_tag, sizeof(poisoned_tag)));

      // Decryption of that ciphertext. Set up both contexts again.
      OPENSSL_memset(&zeroed, 0, sizeof(zeroed));
      OPENSSL_memset(&poisoned, 0x56, sizeof(poisoned));
      OPENSSL_memcpy(&zeroed.gcm_key, &gcm_key, sizeof(gcm_key));
      OPENSSL_memcpy(&poisoned.gcm_key, &gcm_key, sizeof(gcm_key));
      CRYPTO_gcm128_setiv(&zeroed, &aes_key, kIV, iv_len);
      CRYPTO_gcm128_setiv(&poisoned, &aes_key, kIV, iv_len);

      // Decrypt in the same pieces as above.
      ASSERT_TRUE(CRYPTO_gcm128_aad(&zeroed, aad, 5));
      ASSERT_TRUE(CRYPTO_gcm128_aad(&zeroed, aad + 5, sizeof(aad) - 5));
      ASSERT_TRUE(CRYPTO_gcm128_decrypt_ctr32(&zeroed, &aes_key, zeroed_ct,
                                              zeroed_pt, 7, ctr));
      ASSERT_TRUE(CRYPTO_gcm128_decrypt_ctr32(&zeroed, &aes_key, zeroed_ct + 7,
                                              zeroed_pt + 7, sizeof(in) - 7,
                                              ctr));
      CRYPTO_gcm128_tag(&zeroed, zeroed_dec_tag, sizeof(zeroed_dec_tag));
      EXPECT_EQ(Bytes(in, sizeof(in)), Bytes(zeroed_pt, sizeof(zeroed_pt)));
      EXPECT_EQ(Bytes(zeroed_tag, sizeof(zeroed_tag)),
                Bytes(zeroed_dec_tag, sizeof(zeroed_dec_tag)));

      // The same with the 0x56 context.
      ASSERT_TRUE(CRYPTO_gcm128_aad(&poisoned, aad, 5));
      ASSERT_TRUE(CRYPTO_gcm128_aad(&poisoned, aad + 5, sizeof(aad) - 5));
      ASSERT_TRUE(CRYPTO_gcm128_decrypt_ctr32(&poisoned, &aes_key, zeroed_ct,
                                              poisoned_pt, 7, ctr));
      ASSERT_TRUE(CRYPTO_gcm128_decrypt_ctr32(&poisoned, &aes_key,
                                              zeroed_ct + 7, poisoned_pt + 7,
                                              sizeof(in) - 7, ctr));
      CRYPTO_gcm128_tag(&poisoned, poisoned_dec_tag, sizeof(poisoned_dec_tag));
      EXPECT_EQ(Bytes(in, sizeof(in)), Bytes(poisoned_pt, sizeof(poisoned_pt)));
      EXPECT_EQ(Bytes(zeroed_tag, sizeof(zeroed_tag)),
                Bytes(poisoned_dec_tag, sizeof(poisoned_dec_tag)));
    }
  }
}
#endif  // !BORINGSSL_SHARED_LIBRARY

TEST(GCMTest, ByteSwap) {
  EXPECT_EQ(0x04030201u, CRYPTO_bswap4(0x01020304u));
  EXPECT_EQ(UINT64_C(0x0807060504030201),
            CRYPTO_bswap8(UINT64_C(0x0102030405060708)));
}

#if defined(SUPPORTS_ABI_TEST) && !defined(OPENSSL_NO_ASM) && \
    !defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)
TEST(GCMTest, ABI) {
  static const uint64_t kH[2] = {
      UINT64_C(0x66e94bd4ef8a2c3b),
      UINT64_C(0x884cfa59ca342b2e),
  };
  static const size_t kBlockCounts[] = {1, 2, 3, 4, 5, 6, 7, 8, 15, 16, 31, 32};
  uint8_t buf[16 * 32];
  OPENSSL_memset(buf, 42, sizeof(buf));

  uint8_t X[16] = {0x92, 0xa3, 0xb3, 0x60, 0xce, 0xda, 0x88, 0x03,
                   0x78, 0xfe, 0xb2, 0x71, 0xb9, 0xc2, 0x28, 0xf3};

  alignas(16) u128 Htable[16];
#if defined(GHASH_ASM_X86) || defined(GHASH_ASM_X86_64)
  if (CRYPTO_is_SSSE3_capable()) {
    CHECK_ABI_SEH(gcm_init_ssse3, Htable, kH);
    CHECK_ABI_SEH(gcm_gmult_ssse3, X, Htable);
    for (size_t blocks : kBlockCounts) {
      CHECK_ABI_SEH(gcm_ghash_ssse3, X, Htable, buf, 16 * blocks);
    }
  }

  if (crypto_gcm_clmul_enabled()) {
    CHECK_ABI_SEH(gcm_init_clmul, Htable, kH);
    CHECK_ABI_SEH(gcm_gmult_clmul, X, Htable);
    for (size_t blocks : kBlockCounts) {
      CHECK_ABI_SEH(gcm_ghash_clmul, X, Htable, buf, 16 * blocks);
    }

#if defined(GHASH_ASM_X86_64)
    if (CRYPTO_is_AVX_capable() && CRYPTO_is_MOVBE_capable()) {
      CHECK_ABI_SEH(gcm_init_avx, Htable, kH);
      CHECK_ABI_SEH(gcm_gmult_avx, X, Htable);
      for (size_t blocks : kBlockCounts) {
        CHECK_ABI_SEH(gcm_ghash_avx, X, Htable, buf, 16 * blocks);
      }

      if (hwaes_capable()) {
        AES_KEY aes_key;
        static const uint8_t kKey[16] = {0};
        uint8_t iv[16] = {0};

        aes_hw_set_encrypt_key(kKey, 128, &aes_key);
        for (size_t blocks : kBlockCounts) {
          CHECK_ABI_SEH(aesni_gcm_encrypt, buf, buf, blocks * 16, &aes_key, iv,
                        Htable, X);
          CHECK_ABI_SEH(aesni_gcm_encrypt, buf, buf, blocks * 16 + 7, &aes_key,
                        iv, Htable, X);
        }
        aes_hw_set_decrypt_key(kKey, 128, &aes_key);
        for (size_t blocks : kBlockCounts) {
          CHECK_ABI_SEH(aesni_gcm_decrypt, buf, buf, blocks * 16, &aes_key, iv,
                        Htable, X);
          CHECK_ABI_SEH(aesni_gcm_decrypt, buf, buf, blocks * 16 + 7, &aes_key,
                        iv, Htable, X);
        }
      }
    }
#if !defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX)
    if (crypto_gcm_avx512_enabled()) {
      CHECK_ABI_SEH(gcm_init_avx512, Htable, kH);
      CHECK_ABI_SEH(gcm_gmult_avx512, X, Htable);
      for (size_t blocks : kBlockCounts) {
        CHECK_ABI_SEH(gcm_ghash_avx512, X, Htable, buf, 16 * blocks);
      }

      if (hwaes_capable()) {
        AES_KEY aes_key;
        static const uint8_t kKey[16] = {0};

        // aes_gcm_*_avx512 makes assumptions about |GCM128_CONTEXT|'s layout.
        GCM128_CONTEXT gcm;
        memset(&gcm, 0, sizeof(gcm));
        memcpy(&gcm.gcm_key.Htable, Htable, sizeof(Htable));
        memcpy(&gcm.Xi, X, sizeof(X));
        uint8_t iv[16] = {0};

        aes_hw_set_encrypt_key(kKey, 128, &aes_key);

        CHECK_ABI_SEH(gcm_setiv_avx512, &aes_key, &gcm, iv, sizeof(iv));

        for (size_t blocks : kBlockCounts) {
          CHECK_ABI_SEH(aes_gcm_encrypt_avx512, &aes_key, &gcm, &gcm.mres, buf,
                        blocks * 16, buf);
        }
        aes_hw_set_decrypt_key(kKey, 128, &aes_key);
        for (size_t blocks : kBlockCounts) {
          CHECK_ABI_SEH(aes_gcm_decrypt_avx512, &aes_key, &gcm, &gcm.mres, buf,
                        blocks * 16, buf);
        }
      }
    }
#endif // !MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX)
#endif  // GHASH_ASM_X86_64
  }
#endif  // GHASH_ASM_X86 || GHASH_ASM_X86_64

#if defined(GHASH_ASM_ARM)
  if (gcm_neon_capable()) {
    CHECK_ABI(gcm_init_neon, Htable, kH);
    CHECK_ABI(gcm_gmult_neon, X, Htable);
    for (size_t blocks : kBlockCounts) {
      CHECK_ABI(gcm_ghash_neon, X, Htable, buf, 16 * blocks);
    }
  }

  if (gcm_pmull_capable()) {
    CHECK_ABI(gcm_init_v8, Htable, kH);
    CHECK_ABI(gcm_gmult_v8, X, Htable);
    for (size_t blocks : kBlockCounts) {
      CHECK_ABI(gcm_ghash_v8, X, Htable, buf, 16 * blocks);
    }
  }
#endif  // GHASH_ASM_ARM

#if defined(OPENSSL_AARCH64) && defined(HW_GCM)
  if (hwaes_capable() && gcm_pmull_capable()) {
    static const uint8_t kKey[256/8] = {0};
    uint8_t iv[16] = {0};

    {
      AES_KEY aes_key;
      aes_hw_set_encrypt_key(kKey, 128, &aes_key);
      CHECK_ABI(aes128_gcm_enc, buf, sizeof(buf) * 8, buf, (uint64_t *)X, iv,
                (const s2n_bignum_AES_KEY *)&aes_key, (const uint64_t *)Htable);
      CHECK_ABI(aes128_gcm_dec, buf, sizeof(buf) * 8, buf, (uint64_t *)X, iv,
                (const s2n_bignum_AES_KEY *)&aes_key, (const uint64_t *)Htable);
      // |aes192_gcm_{enc,dec}_kernel| handle AES-192 only.
      aes_hw_set_encrypt_key(kKey, 192, &aes_key);
      CHECK_ABI(aes192_gcm_enc_kernel, buf, sizeof(buf) * 8, buf, X, iv,
                &aes_key, Htable);
      CHECK_ABI(aes192_gcm_dec_kernel, buf, sizeof(buf) * 8, buf, X, iv,
                &aes_key, Htable);
      aes_hw_set_encrypt_key(kKey, 256, &aes_key);
      CHECK_ABI(aes256_gcm_enc, buf, sizeof(buf) * 8, buf, (uint64_t *)X, iv,
                (const s2n_bignum_AES_KEY *)&aes_key, (const uint64_t *)Htable);
      CHECK_ABI(aes256_gcm_dec, buf, sizeof(buf) * 8, buf, (uint64_t *)X, iv,
                (const s2n_bignum_AES_KEY *)&aes_key, (const uint64_t *)Htable);
    }
#if defined(HW_GCM_S2N_BIGNUM_8X)
    if (CRYPTO_is_ARMv8_SHA3_capable()) {
      AES_KEY aes_key;
      aes_hw_set_encrypt_key(kKey, 128, &aes_key);
      CHECK_ABI(aes128_gcm_enc_alt, buf, sizeof(buf) * 8, buf, (uint64_t *)X,
                iv, (const s2n_bignum_AES_KEY *)&aes_key,
                (const uint64_t *)Htable);
      CHECK_ABI(aes128_gcm_dec_alt, buf, sizeof(buf) * 8, buf, (uint64_t *)X,
                iv, (const s2n_bignum_AES_KEY *)&aes_key,
                (const uint64_t *)Htable);
      aes_hw_set_encrypt_key(kKey, 256, &aes_key);
      CHECK_ABI(aes256_gcm_enc_alt, buf, sizeof(buf) * 8, buf, (uint64_t *)X,
                iv, (const s2n_bignum_AES_KEY *)&aes_key,
                (const uint64_t *)Htable);
      CHECK_ABI(aes256_gcm_dec_alt, buf, sizeof(buf) * 8, buf, (uint64_t *)X,
                iv, (const s2n_bignum_AES_KEY *)&aes_key,
                (const uint64_t *)Htable);
    }
#endif  // HW_GCM_S2N_BIGNUM_8X
  }
#endif

#if defined(GHASH_ASM_PPC64LE)
  if (CRYPTO_is_PPC64LE_vcrypto_capable()) {
    CHECK_ABI(gcm_init_p8, Htable, kH);
    CHECK_ABI(gcm_gmult_p8, X, Htable);
    for (size_t blocks : kBlockCounts) {
      CHECK_ABI(gcm_ghash_p8, X, Htable, buf, 16 * blocks);
    }
  }
#endif  // GHASH_ASM_PPC64LE
}
#endif  // SUPPORTS_ABI_TEST && !OPENSSL_NO_ASM && !MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX
