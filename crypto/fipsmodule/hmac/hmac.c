/* Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com)
 * All rights reserved.
 *
 * This package is an SSL implementation written
 * by Eric Young (eay@cryptsoft.com).
 * The implementation was written so as to conform with Netscapes SSL.
 *
 * This library is free for commercial and non-commercial use as long as
 * the following conditions are aheared to.  The following conditions
 * apply to all code found in this distribution, be it the RC4, RSA,
 * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
 * included with this distribution is covered by the same copyright terms
 * except that the holder is Tim Hudson (tjh@cryptsoft.com).
 *
 * Copyright remains Eric Young's, and as such any Copyright notices in
 * the code are not to be removed.
 * If this package is used in a product, Eric Young should be given attribution
 * as the author of the parts of the library used.
 * This can be in the form of a textual message at program startup or
 * in documentation (online or textual) provided with the package.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.] */

#include <openssl/hmac.h>

#include <assert.h>
#include <string.h>

#include <openssl/digest.h>
#include <openssl/mem.h>

#include "../../internal.h"


uint8_t *HMAC(const EVP_MD *evp_md, const void *key, size_t key_len,
              const uint8_t *data, size_t data_len, uint8_t *out,
              unsigned int *out_len) {
  // We have to verify that all the HMAC services actually succeed before
  // updating the indicator state, so we lock the state here.
  FIPS_service_indicator_lock_state();
  HMAC_CTX ctx;
  HMAC_CTX_init(&ctx);
  if (!HMAC_Init_ex(&ctx, key, key_len, evp_md, NULL) ||
      !HMAC_Update(&ctx, data, data_len) ||
      !HMAC_Final(&ctx, out, out_len)) {
    out = NULL;
  }
  // Unlock service indicator state and check if HMAC functions have succeeded.
  FIPS_service_indicator_unlock_state();
  if(out) {
    HMAC_verify_service_indicator(evp_md);
  }
  HMAC_CTX_cleanup(&ctx);
  return out;
}

void HMAC_CTX_init(HMAC_CTX *ctx) {
  ctx->md = NULL;
  EVP_MD_CTX_init(&ctx->i_ctx);
  EVP_MD_CTX_init(&ctx->o_ctx);
  EVP_MD_CTX_init(&ctx->md_ctx);
}

HMAC_CTX *HMAC_CTX_new(void) {
  HMAC_CTX *ctx = OPENSSL_malloc(sizeof(HMAC_CTX));
  if (ctx != NULL) {
    HMAC_CTX_init(ctx);
  }
  return ctx;
}

void HMAC_CTX_cleanup(HMAC_CTX *ctx) {
  EVP_MD_CTX_cleanup(&ctx->i_ctx);
  EVP_MD_CTX_cleanup(&ctx->o_ctx);
  EVP_MD_CTX_cleanup(&ctx->md_ctx);
  OPENSSL_cleanse(ctx, sizeof(HMAC_CTX));
}

void HMAC_CTX_free(HMAC_CTX *ctx) {
  if (ctx == NULL) {
    return;
  }

  HMAC_CTX_cleanup(ctx);
  OPENSSL_free(ctx);
}

int HMAC_Init_ex(HMAC_CTX *ctx, const void *key, size_t key_len,
                 const EVP_MD *md, ENGINE *impl) {
  // We have to avoid the underlying SHA services updating the indicator
  // state, so we lock the state here.
  FIPS_service_indicator_lock_state();
  int ret = 0;
  if (md == NULL) {
    md = ctx->md;
  }

  // If either |key| is non-NULL or |md| has changed, initialize with a new key
  // rather than rewinding the previous one.
  //
  // TODO(davidben,eroman): Passing the previous |md| with a NULL |key| is
  // ambiguous between using the empty key and reusing the previous key. There
  // exist callers which intend the latter, but the former is an awkward edge
  // case. Fix to API to avoid this.
  if (md != ctx->md || key != NULL) {
    uint8_t pad[EVP_MAX_MD_BLOCK_SIZE];
    uint8_t key_block[EVP_MAX_MD_BLOCK_SIZE];
    unsigned key_block_len;

    size_t block_size = EVP_MD_block_size(md);
    assert(block_size <= sizeof(key_block));
    if (block_size < key_len) {
      // Long keys are hashed.
      if (!EVP_DigestInit_ex(&ctx->md_ctx, md, impl) ||
          !EVP_DigestUpdate(&ctx->md_ctx, key, key_len) ||
          !EVP_DigestFinal_ex(&ctx->md_ctx, key_block, &key_block_len)) {
        goto end;
      }
    } else {
      assert(key_len <= sizeof(key_block));
      OPENSSL_memcpy(key_block, key, key_len);
      key_block_len = (unsigned)key_len;
    }
    // Keys are then padded with zeros.
    if (key_block_len != EVP_MAX_MD_BLOCK_SIZE) {
      OPENSSL_memset(&key_block[key_block_len], 0, sizeof(key_block) - key_block_len);
    }

    for (size_t i = 0; i < EVP_MAX_MD_BLOCK_SIZE; i++) {
      pad[i] = 0x36 ^ key_block[i];
    }
    if (!EVP_DigestInit_ex(&ctx->i_ctx, md, impl) ||
        !EVP_DigestUpdate(&ctx->i_ctx, pad, EVP_MD_block_size(md))) {
      goto end;
    }

    for (size_t i = 0; i < EVP_MAX_MD_BLOCK_SIZE; i++) {
      pad[i] = 0x5c ^ key_block[i];
    }
    if (!EVP_DigestInit_ex(&ctx->o_ctx, md, impl) ||
        !EVP_DigestUpdate(&ctx->o_ctx, pad, EVP_MD_block_size(md))) {
      goto end;
    }

    ctx->md = md;
  }

  if (!EVP_MD_CTX_copy_ex(&ctx->md_ctx, &ctx->i_ctx)) {
    goto end;
  }
  ret = 1;

end:
  FIPS_service_indicator_unlock_state();
  return ret;
}

int HMAC_Update(HMAC_CTX *ctx, const uint8_t *data, size_t data_len) {
  return EVP_DigestUpdate(&ctx->md_ctx, data, data_len);
}

int HMAC_Final(HMAC_CTX *ctx, uint8_t *out, unsigned int *out_len) {
  // We have to avoid the underlying SHA services updating the indicator state,
  // so we lock the state here.
  FIPS_service_indicator_lock_state();
  unsigned int i;
  uint8_t buf[EVP_MAX_MD_SIZE];

  // TODO(davidben): The only thing that can officially fail here is
  // |EVP_MD_CTX_copy_ex|, but even that should be impossible in this case.
  if (!EVP_DigestFinal_ex(&ctx->md_ctx, buf, &i) ||
      !EVP_MD_CTX_copy_ex(&ctx->md_ctx, &ctx->o_ctx) ||
      !EVP_DigestUpdate(&ctx->md_ctx, buf, i) ||
      !EVP_DigestFinal_ex(&ctx->md_ctx, out, out_len)) {
    *out_len = 0;
    FIPS_service_indicator_unlock_state();
    return 0;
  }

  FIPS_service_indicator_unlock_state();
  HMAC_verify_service_indicator(ctx->md);
  return 1;
}

size_t HMAC_size(const HMAC_CTX *ctx) {
  return EVP_MD_size(ctx->md);
}

int HMAC_CTX_copy_ex(HMAC_CTX *dest, const HMAC_CTX *src) {
  if (!EVP_MD_CTX_copy_ex(&dest->i_ctx, &src->i_ctx) ||
      !EVP_MD_CTX_copy_ex(&dest->o_ctx, &src->o_ctx) ||
      !EVP_MD_CTX_copy_ex(&dest->md_ctx, &src->md_ctx)) {
    return 0;
  }

  dest->md = src->md;
  return 1;
}

void HMAC_CTX_reset(HMAC_CTX *ctx) {
  HMAC_CTX_cleanup(ctx);
  HMAC_CTX_init(ctx);
}

int HMAC_Init(HMAC_CTX *ctx, const void *key, int key_len, const EVP_MD *md) {
  if (key && md) {
    HMAC_CTX_init(ctx);
  }
  return HMAC_Init_ex(ctx, key, key_len, md, NULL);
}

int HMAC_CTX_copy(HMAC_CTX *dest, const HMAC_CTX *src) {
  HMAC_CTX_init(dest);
  return HMAC_CTX_copy_ex(dest, src);
}

// Do I need to check return values in cleanup?
// Can I use the output parameter as scratch in final?
// Do I need to clear out params on failure?
#define AWSLC_IMPLEMENT_HMAC_FNS(HMAC_NAME, HMAC_CTX, MD_NAME, MD_CTX_NAME,    \
                                 HMAC_LEN, BLOCK_SIZE, EVP_MD)                 \
  OPENSSL_EXPORT void HMAC_NAME##_cleanup(HMAC_CTX *ctx) {                     \
    OPENSSL_cleanse(ctx, sizeof(HMAC_CTX));                                    \
    ctx->initialized = 0;                                                      \
  }                                                                            \
                                                                               \
  OPENSSL_EXPORT int HMAC_NAME##_Update(HMAC_CTX *ctx, const uint8_t *data,    \
                                        size_t data_len) {                     \
    assert(ctx->initialized);                                                  \
    return MD_NAME##_Update(&ctx->md_ctx, data, data_len);                     \
  }                                                                            \
                                                                               \
  OPENSSL_EXPORT int HMAC_NAME##_Final(HMAC_CTX *ctx, uint8_t out[HMAC_LEN]) { \
    assert(ctx->initialized);                                                  \
    FIPS_service_indicator_lock_state();                                       \
    int result = 0;                                                            \
    if (!MD_NAME##_Final(out, &ctx->md_ctx)) {                                 \
      goto end;                                                                \
    }                                                                          \
    OPENSSL_memcpy(&ctx->md_ctx, &ctx->o_ctx, sizeof(MD_CTX_NAME));            \
    if (!MD_NAME##_Update(&ctx->md_ctx, out, HMAC_LEN)) {                      \
      goto end;                                                                \
    }                                                                          \
    result = MD_NAME##_Final(out, &ctx->md_ctx);                               \
  end:                                                                         \
    FIPS_service_indicator_unlock_state();                                     \
    if (result) {                                                              \
      HMAC_verify_service_indicator(EVP_MD);                                   \
      return 1;                                                                \
    } else {                                                                   \
      return 0;                                                                \
    }                                                                          \
  }                                                                            \
                                                                               \
  OPENSSL_EXPORT int HMAC_NAME##_Init(HMAC_CTX *ctx, const void *key,          \
                                      size_t key_len) {                        \
    FIPS_service_indicator_lock_state();                                       \
    int result = 0;                                                            \
    if (key != NULL || ctx->initialized != 1) {                                \
      uint8_t pad[BLOCK_SIZE] = {0};                                           \
      uint8_t key_block[BLOCK_SIZE] = {0};                                     \
      if (BLOCK_SIZE < key_len) {                                              \
        if (!MD_NAME##_Init(&ctx->md_ctx) ||                                   \
            !MD_NAME##_Update(&ctx->md_ctx, key, key_len) ||                   \
            !MD_NAME##_Final(key_block, &ctx->md_ctx)) {                       \
          goto end;                                                            \
        }                                                                      \
      } else {                                                                 \
        OPENSSL_memcpy(key_block, key, key_len);                               \
      }                                                                        \
      for (size_t i = 0; i < BLOCK_SIZE; i++) {                                \
        pad[i] = 0x36 ^ key_block[i];                                          \
      }                                                                        \
      if (!MD_NAME##_Init(&ctx->i_ctx) ||                                      \
          !MD_NAME##_Update(&ctx->i_ctx, pad, BLOCK_SIZE)) {                   \
        goto end;                                                              \
      }                                                                        \
      for (size_t i = 0; i < BLOCK_SIZE; i++) {                                \
        pad[i] = 0x5c ^ key_block[i];                                          \
      }                                                                        \
      if (!MD_NAME##_Init(&ctx->o_ctx) ||                                      \
          !MD_NAME##_Update(&ctx->o_ctx, pad, BLOCK_SIZE)) {                   \
        goto end;                                                              \
      }                                                                        \
      ctx->initialized = 1;                                                    \
    }                                                                          \
    OPENSSL_memcpy(&ctx->md_ctx, &ctx->i_ctx, sizeof(MD_CTX_NAME));            \
    result = 1;                                                                \
  end:                                                                         \
    FIPS_service_indicator_unlock_state();                                     \
    return result;                                                             \
  }                                                                            \
  OPENSSL_EXPORT int HMAC_NAME(const void *key, size_t key_len,                \
                               const uint8_t *data, size_t data_len,           \
                               uint8_t out[HMAC_LEN]) {                        \
    FIPS_service_indicator_lock_state();                                       \
    HMAC_CTX ctx = {0};                                                        \
    int result;                                                                \
    result = HMAC_NAME##_Init(&ctx, key, key_len) &&                           \
             HMAC_NAME##_Update(&ctx, data, data_len) &&                       \
             HMAC_NAME##_Final(&ctx, out);                                     \
    FIPS_service_indicator_unlock_state();                                     \
    HMAC_NAME##_cleanup(&ctx);                                                 \
    if (result) {                                                              \
      HMAC_verify_service_indicator(EVP_MD);                                   \
      return 1;                                                                \
    } else {                                                                   \
      return 0;                                                                \
    }                                                                          \
  }

#ifndef OPENSSL_NO_MD4
AWSLC_IMPLEMENT_HMAC_FNS(HMAC_MD4, HMAC_MD4_CTX, MD4, MD4_CTX,
                         MD4_DIGEST_LENGTH, MD4_CBLOCK, EVP_md4())
#endif
#ifndef OPENSSL_NO_MD5
AWSLC_IMPLEMENT_HMAC_FNS(HMAC_MD5, HMAC_MD5_CTX, MD5, MD5_CTX,
                         MD5_DIGEST_LENGTH, MD5_CBLOCK, EVP_md5())
#endif
#ifndef OPENSSL_NO_SHA
AWSLC_IMPLEMENT_HMAC_FNS(HMAC_SHA1, HMAC_SHA1_CTX, SHA1, SHA_CTX,
                         SHA_DIGEST_LENGTH, SHA_CBLOCK, EVP_sha1())
#endif
#ifndef OPENSSL_NO_SHA256
AWSLC_IMPLEMENT_HMAC_FNS(HMAC_SHA224, HMAC_SHA256_CTX, SHA224, SHA256_CTX,
                         SHA224_DIGEST_LENGTH, SHA224_CBLOCK, EVP_sha224())

AWSLC_IMPLEMENT_HMAC_FNS(HMAC_SHA256, HMAC_SHA256_CTX, SHA256, SHA256_CTX,
                         SHA256_DIGEST_LENGTH, SHA256_CBLOCK, EVP_sha256())
#endif
#ifndef OPENSSL_NO_SHA512
AWSLC_IMPLEMENT_HMAC_FNS(HMAC_SHA384, HMAC_SHA512_CTX, SHA384, SHA512_CTX,
                         SHA384_DIGEST_LENGTH, SHA384_CBLOCK, EVP_sha384())

AWSLC_IMPLEMENT_HMAC_FNS(HMAC_SHA512, HMAC_SHA512_CTX, SHA512, SHA512_CTX,
                         SHA512_DIGEST_LENGTH, SHA512_CBLOCK, EVP_sha512())
#endif
#ifndef OPENSSL_NO_RIPEMD
AWSLC_IMPLEMENT_HMAC_FNS(HMAC_RIPEMD160, HMAC_RIPEMD160_CTX, RIPEMD160,
                         RIPEMD160_CTX, RIPEMD160_DIGEST_LENGTH,
                         RIPEMD160_CBLOCK, EVP_ripemd160())
#endif
