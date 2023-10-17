/* Copyright (c) 2018, Google Inc.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

#include <openssl/base.h>

#if defined(BORINGSSL_DISPATCH_TEST) && !defined(BORINGSSL_SHARED_LIBRARY)

#include <functional>
#include <utility>
#include <vector>

#include <openssl/aead.h>
#include <openssl/aes.h>
#include <openssl/sha.h>
#include <openssl/mem.h>

#include <gtest/gtest.h>

#include "internal.h"
#include "fipsmodule/cpucap/internal.h"
#include "fipsmodule/modes/internal.h"


class ImplDispatchTest : public ::testing::Test {
 public:
  void SetUp() override {
#if defined(OPENSSL_X86) || defined(OPENSSL_X86_64)
    aes_hw_ = CRYPTO_is_AESNI_capable();
    avx_movbe_ = CRYPTO_is_AVX_capable() && CRYPTO_is_MOVBE_capable();
    aes_vpaes_ = CRYPTO_is_SSSE3_capable();
    sha_ext_ =
// TODO(CryptoAlg-2137): sha_ext_ isn't enabled on Windows Debug Builds with newer
// 32-bit Intel processors.
#if !(defined(OPENSSL_WINDOWS) && defined(OPENSSL_X86) && !defined(NDEBUG))
    CRYPTO_is_SHAEXT_capable();
#else
    false;
#endif

    vaes_vpclmulqdq_ =
#if !defined(OPENSSL_WINDOWS)
  // crypto_gcm_avx512_enabled excludes Windows
        CRYPTO_is_AVX512_capable() &&
        CRYPTO_is_VAES_capable() &&
        CRYPTO_is_VPCLMULQDQ_capable();
#else
        false;
#endif

    is_x86_64_ =
#if defined(OPENSSL_X86_64)
        true;
#else
        false;
#endif
    is_assembler_too_old =
#if defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX)
        true;
#else
        false;
#endif // MY_ASSEMBLER_IS_TOO_OLD_FOR_AVX
    is_assembler_too_old_avx512 =
#if defined(MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX)
        true;
#else
        false;
#endif // MY_ASSEMBLER_IS_TOO_OLD_FOR_512AVX
#elif defined(OPENSSL_AARCH64)
    aes_hw_ = CRYPTO_is_ARMv8_AES_capable();
    aes_vpaes_ = CRYPTO_is_NEON_capable();
    aes_gcm_pmull_ = CRYPTO_is_ARMv8_PMULL_capable();
    aes_gcm_8x_ = CRYPTO_is_ARMv8_GCM_8x_capable();
    sha_ext_ = OPENSSL_armcap_P & ARMV8_SHA256;
    sha_512_ext_ = OPENSSL_armcap_P & ARMV8_SHA512;
#endif
  }

 protected:
  // AssertFunctionsHit takes a list of pairs (flag index, boolean), and a
  // function to test. It runs the given function and asserts, for each flag
  // index, that the boolean reflects whether that flag index was written or
  // not, and that no other flagged functions were triggered.
  void AssertFunctionsHit(std::vector<std::pair<size_t, bool>> flags,
                          std::function<void()> f) {
    OPENSSL_memset(BORINGSSL_function_hit, 0, sizeof(BORINGSSL_function_hit));

    f();

    for (const auto& flag : flags) {
      SCOPED_TRACE(flag.first);
      ASSERT_LT(flag.first, sizeof(BORINGSSL_function_hit));
      EXPECT_EQ(flag.second, BORINGSSL_function_hit[flag.first] == 1);
      BORINGSSL_function_hit[flag.first] = 0;
    }

    for (size_t i = 0; i < sizeof(BORINGSSL_function_hit); i++) {
      EXPECT_EQ(0u, BORINGSSL_function_hit[i])
          << "Flag " << i << " unexpectedly hit";
    }
  }

  bool aes_hw_ = false;
  bool aes_vpaes_ = false;
  bool sha_ext_ = false;
#if defined(OPENSSL_X86) || defined(OPENSSL_X86_64)
  bool vaes_vpclmulqdq_ = false;
  bool avx_movbe_ = false;
  bool is_x86_64_ = false;
  bool is_assembler_too_old = false;
  bool is_assembler_too_old_avx512 = false;
#else // AARCH64
  bool aes_gcm_pmull_ = false;
  bool aes_gcm_8x_ = false;
  bool sha_512_ext_ = false;
#endif

};

#if !defined(OPENSSL_NO_ASM) && (defined(OPENSSL_X86) || \
    defined(OPENSSL_X86_64) || defined(OPENSSL_AARCH64))

constexpr size_t kFlag_aes_hw_ctr32_encrypt_blocks = 0;
constexpr size_t kFlag_aes_hw_encrypt = 1;
constexpr size_t kFlag_aes_hw_set_encrypt_key = 3;
constexpr size_t kFlag_vpaes_encrypt = 4;
constexpr size_t kFlag_vpaes_set_encrypt_key = 5;
constexpr size_t kFlag_sha256_hw = 6;
#if defined(OPENSSL_X86) || defined(OPENSSL_X86_64)
constexpr size_t kFlag_aesni_gcm_encrypt = 2;
constexpr size_t kFlag_aes_gcm_encrypt_avx512 = 7;
#else // AARCH64
constexpr size_t kFlag_aes_gcm_enc_kernel = 2;
constexpr size_t kFlag_aesv8_gcm_8x_enc_128 = 7;
constexpr size_t kFlag_sha512_hw = 8;
#endif

TEST_F(ImplDispatchTest, AEAD_AES_GCM) {
  AssertFunctionsHit(
      {
          {kFlag_aes_hw_encrypt, aes_hw_},
          {kFlag_aes_hw_set_encrypt_key, aes_hw_},
          {kFlag_vpaes_encrypt, aes_vpaes_ && !aes_hw_},
          {kFlag_vpaes_set_encrypt_key, aes_vpaes_ && !aes_hw_},
#if defined(OPENSSL_X86) || defined(OPENSSL_X86_64)
          {kFlag_aes_hw_ctr32_encrypt_blocks, aes_hw_ &&
           (is_assembler_too_old || !vaes_vpclmulqdq_)},
          {kFlag_aesni_gcm_encrypt,
           is_x86_64_ && aes_hw_ && avx_movbe_ &&
           !is_assembler_too_old && !vaes_vpclmulqdq_},
          {kFlag_aes_gcm_encrypt_avx512,
           is_x86_64_ && aes_hw_ &&
           !is_assembler_too_old_avx512 &&
           vaes_vpclmulqdq_},
#else // AARCH64
          {kFlag_aes_hw_ctr32_encrypt_blocks, aes_hw_ &&
           !aes_gcm_pmull_ && !aes_gcm_8x_},
          {kFlag_aes_gcm_enc_kernel, aes_hw_ &&
           aes_gcm_pmull_ && !aes_gcm_8x_},
          {kFlag_aesv8_gcm_8x_enc_128, aes_hw_ &&
           aes_gcm_pmull_ && aes_gcm_8x_}
#endif
      },
      [] {
        const uint8_t kZeros[16] = {0};
        const uint8_t kPlaintext[256] = {1, 2, 3, 4, 0};
        uint8_t ciphertext[sizeof(kPlaintext) + 16];
        size_t ciphertext_len;
        bssl::ScopedEVP_AEAD_CTX ctx;
        ASSERT_TRUE(EVP_AEAD_CTX_init(ctx.get(), EVP_aead_aes_128_gcm(), kZeros,
                                      sizeof(kZeros),
                                      EVP_AEAD_DEFAULT_TAG_LENGTH, nullptr));
        ASSERT_TRUE(EVP_AEAD_CTX_seal(
            ctx.get(), ciphertext, &ciphertext_len, sizeof(ciphertext), kZeros,
            EVP_AEAD_nonce_length(EVP_aead_aes_128_gcm()), kPlaintext,
            sizeof(kPlaintext), nullptr, 0));
      });
}

TEST_F(ImplDispatchTest, AES_set_encrypt_key) {
  AssertFunctionsHit(
      {
          {kFlag_aes_hw_set_encrypt_key, aes_hw_},
          {kFlag_vpaes_set_encrypt_key, aes_vpaes_ && !aes_hw_},
      },
      [] {
        AES_KEY key;
        static const uint8_t kZeros[16] = {0};
        AES_set_encrypt_key(kZeros, sizeof(kZeros) * 8, &key);
      });
}

TEST_F(ImplDispatchTest, AES_single_block) {
  AES_KEY key;
  static const uint8_t kZeros[16] = {0};
  AES_set_encrypt_key(kZeros, sizeof(kZeros) * 8, &key);

  AssertFunctionsHit(
      {
          {kFlag_aes_hw_encrypt, aes_hw_},
          {kFlag_vpaes_encrypt, aes_vpaes_ && !aes_hw_},
      },
      [&key] {
        uint8_t in[AES_BLOCK_SIZE] = {0};
        uint8_t out[AES_BLOCK_SIZE];
        AES_encrypt(in, out, &key);
      });
}

TEST_F(ImplDispatchTest, SHA256) {
  AssertFunctionsHit(
      {
          {kFlag_sha256_hw, sha_ext_},
      },
      [] {
        const uint8_t in[32] = {0};
        uint8_t out[SHA256_DIGEST_LENGTH];
        SHA256(in, 32, out);
      });
}

#ifdef OPENSSL_AARCH64
TEST_F(ImplDispatchTest, SHA512) {
  AssertFunctionsHit(
      {
          {kFlag_sha512_hw, sha_512_ext_},
      },
      [] {
        const uint8_t in[32] = {0};
        uint8_t out[SHA512_DIGEST_LENGTH];
        SHA512(in, 32, out);
      });
}
#endif // OPENSSL_AARCH64

#endif  // !OPENSSL_NO_ASM && (OPENSSL_X86 || OPENSSL_X86_64 || OPENSSL_AARCH64)

#endif  // DISPATCH_TEST && !SHARED_LIBRARY
