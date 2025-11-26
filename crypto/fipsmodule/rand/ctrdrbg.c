/* Copyright (c) 2017, Google Inc.
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

#include <openssl/aes.h>
#include <openssl/ctrdrbg.h>

#include <openssl/type_check.h>
#include <openssl/mem.h>

#include "internal.h"
#include "../cipher/internal.h"
#include "../delocate.h"
#include "../modes/internal.h"
#include "../service_indicator/internal.h"

// Section references in this file refer to SP 800-90Ar1:
// http://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf

// See table 3.
static const uint64_t kMaxReseedCount = UINT64_C(1) << 48;

// kInitMask is the result of encrypting blocks with big-endian value 1, 2
// and 3 with the all-zero AES-256 key.
static const uint8_t kInitMask[CTR_DRBG_ENTROPY_LEN] = {
    0x53, 0x0f, 0x8a, 0xfb, 0xc7, 0x45, 0x36, 0xb9, 0xa9, 0x63, 0xb4, 0xf1,
    0xc4, 0xcb, 0x73, 0x8b, 0xce, 0xa7, 0x40, 0x3d, 0x4d, 0x60, 0x6b, 0x6e,
    0x07, 0x4e, 0xc5, 0xd3, 0xba, 0xf3, 0x9d, 0x18, 0x72, 0x60, 0x03, 0xca,
    0x37, 0xa6, 0x2a, 0x74, 0xd1, 0xa2, 0xf5, 0x8e, 0x75, 0x06, 0x35, 0x8e,
};

struct generation_nonce {
  uint8_t nonce[CTR_DRBG_NONCE_LEN];
};

DEFINE_BSS_GET(AES_KEY, bcc_key)
DEFINE_BSS_GET(struct generation_nonce, generation_nonce)
DEFINE_STATIC_ONCE(bcc_init_once)
DEFINE_STATIC_MUTEX(generation_nonce_lock)

// Implementation of derivation function assumes CTR_DRBG_ENTROPY_LEN is 48.
// That is, assumes the number of output bytes is 48. In addition, value must be
// a multiple of the AES block size.
OPENSSL_STATIC_ASSERT(CTR_DRBG_ENTROPY_LEN == 48, ctr_drbg_df_assumes_ctr_drbg_entropy_len_is_equal_to_48)
OPENSSL_STATIC_ASSERT(CTR_DRBG_ENTROPY_LEN % AES_BLOCK_SIZE == 0,
                      not_a_multiple_of_AES_block_size)

static void init_df_bcc_once(void) {

  // defined in SP800-90A 10.3.2 (8).
  static const uint8_t staticBccKey[32] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,
  };

  if (AES_set_encrypt_key(staticBccKey, 256, bcc_key_bss_get()) != 0) {
    abort();
  }
}

// Increments 32-bit number starting at *in. Assumes big-endian increment.
static void u32_add_one(uint8_t *in) {
  uint32_t ctr = CRYPTO_load_u32_be(in);
  CRYPTO_store_u32_be(in, ctr + 1);
}

// df_bcc implements BCC from SP800-90A 10.3.3. This algorithm is CBC-mode but
// only keeping the last resulting block. |input_len| must be a multiple of the
// AES block size (16) and non-zero. |output| must be zeroised.
// Return 1 on success, 0 otherwise.
static int df_bcc(uint8_t *input, size_t input_len,
  uint8_t output[AES_BLOCK_SIZE], AES_KEY *key) {

  if (input_len < AES_BLOCK_SIZE || input_len % AES_BLOCK_SIZE != 0) {
    return 0;
  }

  for (size_t block = 0; block < input_len; block += AES_BLOCK_SIZE) {
    CRYPTO_xor16(output, output, &input[block]);
    AES_encrypt(output, output, key);
  }
  return 1;
}

// CTR_DRBG_df implements the block cipher derivation function from SP800-90A
// 10.3.2 assuming a constant keylen of 256, block size of 16, and output length
// of |CTR_DRBG_ENTROPY_LEN|. Arguments |entropy_input| and may alias
// |entropy_output| but not partially overlap.
// Returns 1 on success, 0 otherwise.
static int CTR_DRBG_df(CTR_DRBG_STATE *drbg,
                uint8_t *entropy_input, size_t entropy_input_len,
                uint8_t entropy_output[CTR_DRBG_ENTROPY_LEN]) {

  int ret = 0;

  if (drbg == NULL ||
      entropy_input == NULL ||
      entropy_output == NULL ||
      entropy_input_len == 0) {
    return 0;
  }

  // 10.3.2 (8) is constant when key length is constant. Initialise an AES
  // object once which can be used read-only by all threads. 
  CRYPTO_once(bcc_init_once_bss_get(), init_df_bcc_once);

  // Generally, integer values for 10.3.2 must be representable by a
  // 32-bit integer. First condition is to capture cases were the size_t type
  // is smaller than 0xFFFFFFFF e.g. 32-bit Android and the compiler throwing
  // warnings.
  if (SIZE_MAX > UINT32_MAX && entropy_input_len > UINT32_MAX) {
    return 0;
  }

  // The derivation function can be split into two phases:
  // A) Run BCC to extract.
  // B) Run block cipher iteratively to expand.
  //
  // We first handle phase (A). The goal is to construct strings IV and S, that
  // are used as input to BCC. IV and S are composed of the following values:
  // i, L, N (32-bit represented)
  // 10.3.2 (2): L = entropy_input_len
  // 10.3.2 (3): N = CTR_DRBG_ENTROPY_LEN
  // 10.3.2 (4+5): S = L || N || input_string || 0x80 || 0x00-padded to block size
  // 10.3.2 (9.1): IV = i || 0x00-padded to block size
  //
  // Using these values, we construct IV_S = IV || S used in 10.3.2 (9.2).

  static const size_t df_s_prefix_length = 2 * sizeof(uint32_t); // 2x 32-bit integers
  // Compute required zero-padding (might be zero). +1 because of 0x80
  // delimiter in S.
  size_t df_s_zero_padding = (-(df_s_prefix_length + entropy_input_len + 1)) & (AES_BLOCK_SIZE-1);

  // Knowing the padding, we can compute the full length of S.
  size_t df_s_length = df_s_prefix_length + entropy_input_len + 1 + df_s_zero_padding;

  // Since the length of the IV is fixed when the output length is fixed, we can
  // compute the length of IV || S.
  static const size_t df_iv_length = AES_BLOCK_SIZE;
  size_t df_iv_s_length = df_iv_length + df_s_length;

  // Zeroise to avoid zero padding later.
  uint8_t *IV_S = OPENSSL_zalloc(df_iv_s_length);
  if (IV_S == NULL) {
    return 0;
  }

  // IV_S = IV || L || N || entropy_input
  CRYPTO_store_u32_be(IV_S + df_iv_length, (uint32_t) entropy_input_len);
  CRYPTO_store_u32_be(IV_S + df_iv_length + sizeof(uint32_t), (uint32_t) CTR_DRBG_ENTROPY_LEN);
  OPENSSL_memcpy(IV_S + df_iv_length + df_s_prefix_length, entropy_input, entropy_input_len);

  // IV_S = IV || L || N || entropy_input || 0x80
  // Implicitly, zero-padded.
  IV_S[df_iv_length + df_s_prefix_length + entropy_input_len] = 0x80;

  // We now have the input for BCC. In our case, keylen + outlen = 32 + 16 = 48
  // and len(temp) = block size = 16. Which means invoking BCC(K, (IV || S))
  // 3 times. Each iteration requires |S || IV|/16 block cipher invocations. Use
  // encrypt_output to save an extra temporary buffer.
  AES_KEY *bcc_key_p = bcc_key_bss_get();

  OPENSSL_cleanse(entropy_output, CTR_DRBG_ENTROPY_LEN);
  if (df_bcc(IV_S, df_iv_s_length, entropy_output, bcc_key_p) != 1) {
    goto out;
  }
  u32_add_one(IV_S);
  if (df_bcc(IV_S, df_iv_s_length, entropy_output + AES_BLOCK_SIZE, bcc_key_p) != 1) {
    goto out;
  }
  u32_add_one(IV_S);
  if (df_bcc(IV_S, df_iv_s_length, entropy_output + 2*AES_BLOCK_SIZE, bcc_key_p) != 1) {
    goto out;
  }

  // Phase 2 uses the AES block cipher to expand output to the length requested.
  // Since we assume the output is always CTR_DRBG_ENTROPY_LEN this phase will
  // always need exactly 3 AES block cipher invocations. This sub-algorithm is
  // functionally equivalent to executing CBC-mode with all zero input. We can
  // run this in-place to save an extra temporary buffer.
  //
  // The key is derived from the 32 left-most bytes of BCC output per
  // 10.3.2 (10). K = entropy_output[0:2*AES_BLOCK_SIZE-1]
  AES_KEY block_encrypt_key;
  AES_set_encrypt_key(entropy_output, 256, &block_encrypt_key);

  // The initial input is the remaining 16 right-most bytes of BCC output per
  // 10.3.2 (11). X = entropy_output[2*AES_BLOCK_SIZE:3*AES_BLOCK_SIZE-1].
  AES_encrypt(entropy_output + 2*AES_BLOCK_SIZE, entropy_output, &block_encrypt_key);
  AES_encrypt(entropy_output, entropy_output + AES_BLOCK_SIZE, &block_encrypt_key);
  AES_encrypt(entropy_output + AES_BLOCK_SIZE, entropy_output + 2*AES_BLOCK_SIZE, &block_encrypt_key);

  ret = 1;

out:
  OPENSSL_free(IV_S);
  // used as temporary buffer
  if (ret == 0) {
    OPENSSL_cleanse(entropy_output, CTR_DRBG_ENTROPY_LEN);
  }
  return ret;
}

CTR_DRBG_STATE *CTR_DRBG_new(const uint8_t entropy[CTR_DRBG_ENTROPY_LEN],
                             const uint8_t *personalization,
                             size_t personalization_len) {
  SET_DIT_AUTO_RESET;
  CTR_DRBG_STATE *drbg = OPENSSL_malloc(sizeof(CTR_DRBG_STATE));
  if (drbg == NULL ||
      !CTR_DRBG_init(drbg, entropy, personalization, personalization_len)) {
    CTR_DRBG_free(drbg);
    return NULL;
  }

  return drbg;
}

void CTR_DRBG_free(CTR_DRBG_STATE *state) {
  SET_DIT_AUTO_RESET;
  OPENSSL_free(state);
}

int CTR_DRBG_init(CTR_DRBG_STATE *drbg,
                  const uint8_t entropy[CTR_DRBG_ENTROPY_LEN],
                  const uint8_t *personalization, size_t personalization_len) {
  SET_DIT_AUTO_RESET;
  // Section 10.2.1.3.1
  if (personalization_len > CTR_DRBG_ENTROPY_LEN) {
    return 0;
  }

  uint8_t seed_material[CTR_DRBG_ENTROPY_LEN];
  OPENSSL_memcpy(seed_material, entropy, CTR_DRBG_ENTROPY_LEN);

  for (size_t i = 0; i < personalization_len; i++) {
    seed_material[i] ^= personalization[i];
  }

  // Section 10.2.1.2
  for (size_t i = 0; i < sizeof(kInitMask); i++) {
    seed_material[i] ^= kInitMask[i];
  }

  drbg->ctr = aes_ctr_set_key(&drbg->ks, NULL, &drbg->block, seed_material, 32);
  OPENSSL_memcpy(drbg->counter, seed_material + 32, 16);
  drbg->reseed_counter = 1;

  return 1;
}

static void nonce_increment(uint8_t counter[CTR_DRBG_NONCE_LEN]) {
  size_t index = CTR_DRBG_NONCE_LEN, carry = 1;

  if (counter == NULL) {
    abort();
  }

  do {
    --index;
    carry += counter[index];
    counter[index] = (uint8_t) carry;
    carry >>= 8;
  } while (index);
}

void CTR_DRBG_get_nonce(uint8_t nonce[CTR_DRBG_NONCE_LEN]) {
  OPENSSL_STATIC_ASSERT(CTR_DRBG_NONCE_LEN == 16, ctr_drbg_nonce_len_is_not_16)

  CRYPTO_STATIC_MUTEX_lock_write(generation_nonce_lock_bss_get());
  struct generation_nonce *const nonce_counter_ptr = generation_nonce_bss_get();
  OPENSSL_memcpy(nonce, nonce_counter_ptr->nonce, CTR_DRBG_NONCE_LEN);
  nonce_increment(nonce_counter_ptr->nonce);
  CRYPTO_STATIC_MUTEX_unlock_write(generation_nonce_lock_bss_get());
}

int CTR_DRBG_init_df(CTR_DRBG_STATE *drbg,
                  const uint8_t entropy[CTR_DRBG_ENTROPY_LEN],
                  const uint8_t *personalization, size_t personalization_len,
                  const uint8_t nonce[CTR_DRBG_NONCE_LEN]) {
  SET_DIT_AUTO_RESET;

  if (buffers_alias(entropy, CTR_DRBG_ENTROPY_LEN,
                    personalization, personalization_len)) {
    return 0;
  }

  // Section 10.2.1.3.1
  if (personalization_len > CTR_DRBG_ENTROPY_LEN) {
    return 0;
  }

  uint8_t seed_material[2 * CTR_DRBG_ENTROPY_LEN + CTR_DRBG_NONCE_LEN];
  OPENSSL_memcpy(seed_material, entropy, CTR_DRBG_ENTROPY_LEN);
  OPENSSL_memcpy(seed_material + CTR_DRBG_ENTROPY_LEN, nonce, CTR_DRBG_NONCE_LEN);
  OPENSSL_memcpy(seed_material + CTR_DRBG_ENTROPY_LEN + CTR_DRBG_NONCE_LEN, personalization, personalization_len);

  if (CTR_DRBG_df(drbg, seed_material,
      CTR_DRBG_ENTROPY_LEN + CTR_DRBG_NONCE_LEN + personalization_len, seed_material) != 1) {
    return 0;
  }

  // Section 10.2.1.2
  for (size_t i = 0; i < sizeof(kInitMask); i++) {
    seed_material[i] ^= kInitMask[i];
  }

  drbg->ctr = aes_ctr_set_key(&drbg->ks, NULL, &drbg->block, seed_material, 32);
  OPENSSL_memcpy(drbg->counter, seed_material + 32, 16);
  drbg->reseed_counter = 1;

  return 1;
}

// ctr_inc adds |n| to the last four bytes of |drbg->counter|, treated as a
// big-endian number.
static void ctr32_add(CTR_DRBG_STATE *drbg, uint32_t n) {
  uint32_t ctr = CRYPTO_load_u32_be(drbg->counter + 12);
  CRYPTO_store_u32_be(drbg->counter + 12, ctr + n);
}

static int ctr_drbg_update(CTR_DRBG_STATE *drbg, const uint8_t *data,
                           size_t data_len) {
  // Per section 10.2.1.2, |data_len| must be |CTR_DRBG_ENTROPY_LEN|. Here, we
  // allow shorter inputs and right-pad them with zeros. This is equivalent to
  // the specified algorithm but saves a copy in |CTR_DRBG_generate|.
  if (data_len > CTR_DRBG_ENTROPY_LEN) {
    return 0;
  }

  uint8_t temp[CTR_DRBG_ENTROPY_LEN];
  for (size_t i = 0; i < CTR_DRBG_ENTROPY_LEN; i += AES_BLOCK_SIZE) {
    ctr32_add(drbg, 1);
    drbg->block(drbg->counter, temp + i, &drbg->ks);
  }

  for (size_t i = 0; i < data_len; i++) {
    temp[i] ^= data[i];
  }

  drbg->ctr = aes_ctr_set_key(&drbg->ks, NULL, &drbg->block, temp, 32);
  OPENSSL_memcpy(drbg->counter, temp + 32, 16);

  return 1;
}

int CTR_DRBG_reseed(CTR_DRBG_STATE *drbg,
                    const uint8_t entropy[CTR_DRBG_ENTROPY_LEN],
                    const uint8_t *additional_data,
                    size_t additional_data_len) {
  SET_DIT_AUTO_RESET;
  // Section 10.2.1.4
  uint8_t entropy_copy[CTR_DRBG_ENTROPY_LEN];

  if (additional_data_len > 0) {
    if (additional_data_len > CTR_DRBG_ENTROPY_LEN) {
      return 0;
    }

    OPENSSL_memcpy(entropy_copy, entropy, CTR_DRBG_ENTROPY_LEN);
    for (size_t i = 0; i < additional_data_len; i++) {
      entropy_copy[i] ^= additional_data[i];
    }

    entropy = entropy_copy;
  }

  if (!ctr_drbg_update(drbg, entropy, CTR_DRBG_ENTROPY_LEN)) {
    return 0;
  }

  drbg->reseed_counter = 1;

  return 1;
}

int CTR_DRBG_reseed_df(CTR_DRBG_STATE *drbg,
                    const uint8_t entropy[CTR_DRBG_ENTROPY_LEN],
                    const uint8_t *additional_data,
                    size_t additional_data_len) {
  SET_DIT_AUTO_RESET;
  int ret = 0;

  if (buffers_alias(entropy, CTR_DRBG_ENTROPY_LEN,
                    additional_data, additional_data_len)) {
    return 0;
  }

  if (additional_data_len > CTR_DRBG_ENTROPY_LEN) {
    return 0;
  }

  uint8_t entropy_copy[2 * CTR_DRBG_ENTROPY_LEN];
  OPENSSL_memcpy(entropy_copy, entropy, CTR_DRBG_ENTROPY_LEN);
  OPENSSL_memcpy(entropy_copy + CTR_DRBG_ENTROPY_LEN, additional_data, additional_data_len);

  if (CTR_DRBG_df(drbg, entropy_copy, CTR_DRBG_ENTROPY_LEN + additional_data_len,
      entropy_copy) != 1) {
    goto out;
  }

  if (!ctr_drbg_update(drbg, entropy_copy, CTR_DRBG_ENTROPY_LEN)) {
    goto out;
  }

  drbg->reseed_counter = 1;
  ret = 1;

out:
  OPENSSL_cleanse(entropy_copy, 2 * CTR_DRBG_ENTROPY_LEN);
  return ret;
}

int CTR_DRBG_generate(CTR_DRBG_STATE *drbg, uint8_t *out, size_t out_len,
                      const uint8_t *additional_data,
                      size_t additional_data_len) {
  SET_DIT_AUTO_RESET;
  // See 9.3.1
  if (out_len > CTR_DRBG_MAX_GENERATE_LENGTH) {
    return 0;
  }

  // See 10.2.1.5.1
  if (drbg->reseed_counter > kMaxReseedCount) {
    return 0;
  }

  if (additional_data_len != 0 &&
      !ctr_drbg_update(drbg, additional_data, additional_data_len)) {
    return 0;
  }

  // kChunkSize is used to interact better with the cache. Since the AES-CTR
  // code assumes that it's encrypting rather than just writing keystream, the
  // buffer has to be zeroed first. Without chunking, large reads would zero
  // the whole buffer, flushing the L1 cache, and then do another pass (missing
  // the cache every time) to “encrypt” it. The code can avoid this by
  // chunking.
  static const size_t kChunkSize = 8 * 1024;

  while (out_len >= AES_BLOCK_SIZE) {
    size_t todo = kChunkSize;
    if (todo > out_len) {
      todo = out_len;
    }

    todo &= ~(AES_BLOCK_SIZE-1);
    const size_t num_blocks = todo / AES_BLOCK_SIZE;

    if (drbg->ctr) {
      OPENSSL_memset(out, 0, todo);
      ctr32_add(drbg, 1);
      drbg->ctr(out, out, num_blocks, &drbg->ks, drbg->counter);
      ctr32_add(drbg, (uint32_t)(num_blocks - 1));
    } else {
      for (size_t i = 0; i < todo; i += AES_BLOCK_SIZE) {
        ctr32_add(drbg, 1);
        drbg->block(drbg->counter, out + i, &drbg->ks);
      }
    }

    out += todo;
    out_len -= todo;
  }

  if (out_len > 0) {
    uint8_t block[AES_BLOCK_SIZE];
    ctr32_add(drbg, 1);
    drbg->block(drbg->counter, block, &drbg->ks);

    OPENSSL_memcpy(out, block, out_len);
  }

  // Right-padding |additional_data| in step 2.2 is handled implicitly by
  // |ctr_drbg_update|, to save a copy.
  if (!ctr_drbg_update(drbg, additional_data, additional_data_len)) {
    return 0;
  }

  drbg->reseed_counter++;
  FIPS_service_indicator_update_state();
  return 1;
}

int CTR_DRBG_generate_df(CTR_DRBG_STATE *drbg, uint8_t *out, size_t out_len,
                      const uint8_t *additional_data,
                      size_t additional_data_len) {
  SET_DIT_AUTO_RESET;
  // See 9.3.1
  if (out_len > CTR_DRBG_MAX_GENERATE_LENGTH ||
      additional_data_len > CTR_DRBG_ENTROPY_LEN) {
    return 0;
  }

  // See 10.2.1.5.1
  if (drbg->reseed_counter > kMaxReseedCount) {
    return 0;
  }

  uint8_t df_entropy[CTR_DRBG_ENTROPY_LEN];
  if (additional_data_len != 0) {
    OPENSSL_memcpy(df_entropy, additional_data, additional_data_len);
    if (CTR_DRBG_df(drbg, df_entropy, additional_data_len, df_entropy) != 1) {
      return 0;
    }
    if (!ctr_drbg_update(drbg, df_entropy, CTR_DRBG_ENTROPY_LEN)) {
      return 0;
    }
  }

  // kChunkSize is used to interact better with the cache. Since the AES-CTR
  // code assumes that it's encrypting rather than just writing keystream, the
  // buffer has to be zeroed first. Without chunking, large reads would zero
  // the whole buffer, flushing the L1 cache, and then do another pass (missing
  // the cache every time) to “encrypt” it. The code can avoid this by
  // chunking.
  static const size_t kChunkSize = 8 * 1024;

  while (out_len >= AES_BLOCK_SIZE) {
    size_t todo = kChunkSize;
    if (todo > out_len) {
      todo = out_len;
    }

    todo &= ~(AES_BLOCK_SIZE-1);
    const size_t num_blocks = todo / AES_BLOCK_SIZE;

    if (drbg->ctr) {
      OPENSSL_memset(out, 0, todo);
      ctr32_add(drbg, 1);
      drbg->ctr(out, out, num_blocks, &drbg->ks, drbg->counter);
      ctr32_add(drbg, (uint32_t)(num_blocks - 1));
    } else {
      for (size_t i = 0; i < todo; i += AES_BLOCK_SIZE) {
        ctr32_add(drbg, 1);
        drbg->block(drbg->counter, out + i, &drbg->ks);
      }
    }

    out += todo;
    out_len -= todo;
  }

  if (out_len > 0) {
    uint8_t block[AES_BLOCK_SIZE];
    ctr32_add(drbg, 1);
    drbg->block(drbg->counter, block, &drbg->ks);

    OPENSSL_memcpy(out, block, out_len);
  }

  // Use additional_data buffer is no additional data because it's already
  // zeroised.
  if (!ctr_drbg_update(drbg, df_entropy,
      additional_data_len ? CTR_DRBG_ENTROPY_LEN : 0)) {
    return 0;
  }

  drbg->reseed_counter++;
  FIPS_service_indicator_update_state();

  return 1;
}

void CTR_DRBG_clear(CTR_DRBG_STATE *drbg) {
  OPENSSL_cleanse(drbg, sizeof(CTR_DRBG_STATE));
}
