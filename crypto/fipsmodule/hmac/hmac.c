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

typedef int (*HmacInplaceOneShot)(const void *, size_t, const uint8_t *, size_t, uint8_t *);
typedef int (*HmacInPlaceInit)(void *, const void *, size_t);
typedef int (*HmacInPlaceUpdate)(void *,const uint8_t *, size_t);
typedef int (*HmacInPlaceFinal)(void *, uint8_t *);
typedef void (*HmacInPlaceCleanup)(void *);
typedef struct in_place_methods_st InPlaceMethods;

struct in_place_methods_st {
  int md_nid;
  size_t ctxSize;
  HmacInplaceOneShot oneShot;
  HmacInPlaceInit init;
  HmacInPlaceUpdate update;
  HmacInPlaceFinal digest;  // Not named final to avoid keywords
  HmacInPlaceCleanup cleanup;
};

#define DEFINE_IN_PLACE_METHODS(HMAC_NAME, CTX_NAME, EVP_MD_NID)\
  {                                                             \
    .md_nid = EVP_MD_NID,                                       \
    .ctxSize = sizeof(CTX_NAME),                                \
    .oneShot = (HmacInplaceOneShot)(HMAC_NAME),                 \
    .init = (HmacInPlaceInit)(HMAC_NAME##_Init),                \
    .update = (HmacInPlaceUpdate)(HMAC_NAME##_Update),          \
    .digest = (HmacInPlaceFinal)(HMAC_NAME##_Final),            \
    .cleanup = (HmacInPlaceCleanup)(HMAC_NAME##_cleanup)        \
  }

static InPlaceMethods kInPlaceMethods[] = {
#ifndef OPENSSL_NO_MD4
    DEFINE_IN_PLACE_METHODS(HMAC_MD4, HMAC_MD4_CTX, NID_md4),
#endif
#ifndef OPENSSL_NO_MD5
    DEFINE_IN_PLACE_METHODS(HMAC_MD5, HMAC_MD5_CTX, NID_md5),
#endif
#ifndef OPENSSL_NO_SHA
    DEFINE_IN_PLACE_METHODS(HMAC_SHA1, HMAC_SHA1_CTX, NID_sha1),
#endif
#ifndef OPENSSL_NO_SHA256
    DEFINE_IN_PLACE_METHODS(HMAC_SHA224, HMAC_SHA256_CTX, NID_sha224),
    DEFINE_IN_PLACE_METHODS(HMAC_SHA256, HMAC_SHA256_CTX, NID_sha256),
#endif
#ifndef OPENSSL_NO_SHA512
    DEFINE_IN_PLACE_METHODS(HMAC_SHA384, HMAC_SHA512_CTX, NID_sha384),
    DEFINE_IN_PLACE_METHODS(HMAC_SHA512, HMAC_SHA512_CTX, NID_sha512),
#endif
#ifndef OPENSSL_NO_RIPEMD
    DEFINE_IN_PLACE_METHODS(HMAC_RIPEMD160, HMAC_RIPEMD160_CTX, NID_ripe160),
#endif
    {.md_nid = 0,
     .ctxSize = 0,
     .oneShot = NULL,
     .init = NULL,
     .update = NULL,
     .digest = NULL,
     .cleanup = NULL}};

static const InPlaceMethods *GetInPlaceMethods(const EVP_MD *evp_md) {
  InPlaceMethods *result = kInPlaceMethods;
  while (result->md_nid != evp_md->type && result->md_nid != 0) {
    result++;
  }
  return result;
}


uint8_t *HMAC(const EVP_MD *evp_md, const void *key, size_t key_len,
              const uint8_t *data, size_t data_len, uint8_t *out,
              unsigned int *out_len) {
  const InPlaceMethods* inPlace = GetInPlaceMethods(evp_md);
  if (inPlace->md_nid == 0) {
    // This indicates that we do not support this digest
    return NULL;
  }
  if (inPlace->oneShot(key, key_len, data, data_len, out)) {
    if (out_len) {
      *out_len = EVP_MD_size(evp_md);
    }
    return out;
  } else {
    return NULL;
  }
}

void HMAC_CTX_init(HMAC_CTX *ctx) {
  OPENSSL_memset(ctx, 0, sizeof(HMAC_CTX));
}

HMAC_CTX *HMAC_CTX_new(void) {
  HMAC_CTX *ctx = OPENSSL_malloc(sizeof(HMAC_CTX));
  if (ctx != NULL) {
    HMAC_CTX_init(ctx);
  }
  return ctx;
}

void HMAC_CTX_cleanup(HMAC_CTX *ctx) {
  // All of the contexts are flat and can simply be zeroed
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
  // TODO: Figure out how we want to handle engines in this case.
  assert(impl == NULL);

  // There is nothing left to clean, do we need to allocate a new contet?
  if (md && ctx->md != md) {
    ctx->methods = GetInPlaceMethods(md);
    if (ctx->methods->md_nid == 0) {
      // Unsupported md
      ctx->methods = NULL;
      return 0;
    }

    OPENSSL_memset(&ctx->ctx, 0, sizeof(ctx->ctx));
    assert(ctx->methods->ctxSize > sizeof(ctx->ctx));
    ctx->md = md;
  }
  // At this point we know we have valid methods and a context allocated.
  return ctx->methods->init(&ctx->ctx, key, key_len);
}

int HMAC_Update(HMAC_CTX *ctx, const uint8_t *data, size_t data_len) {
  if (ctx->methods == NULL) {
    return 0;
  }
  return ctx->methods->update(&ctx->ctx, data, data_len);
}

int HMAC_Final(HMAC_CTX *ctx, uint8_t *out, unsigned int *out_len) {
  if (ctx->methods == NULL) {
    return 0;
  }
  int result = ctx->methods->digest(&ctx->ctx, out);
  if (result && out_len) {
    *out_len = EVP_MD_size(ctx->md);
  }
  return result;
}

size_t HMAC_size(const HMAC_CTX *ctx) {
  return EVP_MD_size(ctx->md);
}

int HMAC_CTX_copy_ex(HMAC_CTX *dest, const HMAC_CTX *src) {
  OPENSSL_memcpy(dest, src, sizeof(HMAC_CTX));
  return 1;
}

void HMAC_CTX_reset(HMAC_CTX *ctx) {
  HMAC_CTX_cleanup(ctx);
  // Cleanup intrinsicly inits to all zeros which is valid
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
    assert(BLOCK_SIZE % 8 == 0);                                               \
    FIPS_service_indicator_lock_state();                                       \
    int result = 0;                                                            \
    if (key != NULL || ctx->initialized != 1) {                                \
      uint64_t pad[BLOCK_SIZE / 8] = {0};                                      \
      uint64_t key_block[BLOCK_SIZE / 8] = {0};                                \
      if (BLOCK_SIZE < key_len) {                                              \
        if (!MD_NAME##_Init(&ctx->md_ctx) ||                                   \
            !MD_NAME##_Update(&ctx->md_ctx, key, key_len) ||                   \
            !MD_NAME##_Final((uint8_t *) key_block, &ctx->md_ctx)) {           \
          goto end;                                                            \
        }                                                                      \
      } else {                                                                 \
        OPENSSL_memcpy(key_block, key, key_len);                               \
      }                                                                        \
      for (size_t i = 0; i < BLOCK_SIZE / 8; i++) {                            \
        pad[i] = 0x3636363636363636 ^ key_block[i];                            \
      }                                                                        \
      if (!MD_NAME##_Init(&ctx->i_ctx) ||                                      \
          !MD_NAME##_Update(&ctx->i_ctx, pad, BLOCK_SIZE)) {                   \
        goto end;                                                              \
      }                                                                        \
      for (size_t i = 0; i < BLOCK_SIZE / 8; i++) {                            \
        pad[i] = 0x5c5c5c5c5c5c5c5c ^ key_block[i];                            \
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
