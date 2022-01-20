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

typedef int (*HashInit)(void *);
typedef int (*HashUpdate)(void *, const void*, size_t);
typedef int (*HashFinal)(uint8_t *, void*);

struct hmac_methods_st {
  const EVP_MD* evp_md;
  HashInit init;
  HashUpdate update;
  HashFinal finalize; // Not named final to avoid keywords
};

// The maximum number of HMAC implementations
#define HMAC_METHOD_MAX 9

// We need trampolines from the generic void* methods we use to the properly typed underlying methods.
// Without these methods some control flow integrity checks will fail because the function pointer types
// do not exactly match the destination functions. (Namely function pointers use void* pointers for the contexts)
// while the destination functions have specific pointer types for the relevant contexts.
//
// This also includes hash-specific static assertions as they can be added.
#define MD_TRAMPOLINES_EXPLICIT(HASH_NAME, CTX_PREFIX)                        \
  static int AWS_LC_TRAMPOLINE_##HASH_NAME##_Init(void *);                    \
  static int AWS_LC_TRAMPOLINE_##HASH_NAME##_Update(void *, const void *,     \
                                                    size_t);                  \
  static int AWS_LC_TRAMPOLINE_##HASH_NAME##_Final(uint8_t *, void *);        \
  static int AWS_LC_TRAMPOLINE_##HASH_NAME##_Init(void *ctx) {                \
    return HASH_NAME##_Init((CTX_PREFIX##_CTX *)ctx);                         \
  }                                                                           \
  static int AWS_LC_TRAMPOLINE_##HASH_NAME##_Update(                          \
      void *ctx, const void *key, size_t key_len) {                           \
    return HASH_NAME##_Update((CTX_PREFIX##_CTX *)ctx, key, key_len);         \
  }                                                                           \
  static int AWS_LC_TRAMPOLINE_##HASH_NAME##_Final(uint8_t *out, void *ctx) { \
    return HASH_NAME##_Final(out, (CTX_PREFIX##_CTX *)ctx);                   \
  }                                                                           \
  OPENSSL_STATIC_ASSERT(CTX_PREFIX##_CBLOCK % 8 == 0,                         \
                        HASH_NAME##_has_blocksize_not_divisible_by_eight_t)   \
  OPENSSL_STATIC_ASSERT(CTX_PREFIX##_CBLOCK <= EVP_MAX_MD_BLOCK_SIZE,         \
                        HASH_NAME##_has_overlarge_blocksize_t)                \
  OPENSSL_STATIC_ASSERT(                                                      \
      sizeof(CTX_PREFIX##_CTX) <= sizeof(union md_ctx_union),                 \
      HASH_NAME##_has_overlarge_context_t)

#define MD_TRAMPOLINES(HASH_NAME) MD_TRAMPOLINES_EXPLICIT(HASH_NAME, HASH_NAME)

MD_TRAMPOLINES(MD4);
MD_TRAMPOLINES(MD5);
MD_TRAMPOLINES_EXPLICIT(SHA1, SHA);
MD_TRAMPOLINES_EXPLICIT(SHA224, SHA256);
MD_TRAMPOLINES(SHA256);
MD_TRAMPOLINES_EXPLICIT(SHA384, SHA512);
MD_TRAMPOLINES(SHA512);
MD_TRAMPOLINES_EXPLICIT(SHA512_256, SHA512);

struct hmac_method_array_st {
  HmacMethods methods[HMAC_METHOD_MAX];
};

#define DEFINE_IN_PLACE_METHODS(EVP_MD, HASH_NAME)  {                   \
    out->methods[idx].evp_md = EVP_MD;                                  \
    out->methods[idx].init = AWS_LC_TRAMPOLINE_##HASH_NAME##_Init;      \
    out->methods[idx].update = AWS_LC_TRAMPOLINE_##HASH_NAME##_Update;  \
    out->methods[idx].finalize = AWS_LC_TRAMPOLINE_##HASH_NAME##_Final; \
    idx++;                                                              \
    assert(idx <= HMAC_METHOD_MAX);                                     \
  }

DEFINE_LOCAL_DATA(struct hmac_method_array_st, AWSLC_hmac_in_place_methods) {
  OPENSSL_memset((void*) out->methods, 0, sizeof(out->methods));
  int idx = 0;
  DEFINE_IN_PLACE_METHODS(EVP_md4(), MD4);
  DEFINE_IN_PLACE_METHODS(EVP_md5(), MD5);
  DEFINE_IN_PLACE_METHODS(EVP_sha1(), SHA1);
  DEFINE_IN_PLACE_METHODS(EVP_sha224(), SHA224);
  DEFINE_IN_PLACE_METHODS(EVP_sha256(), SHA256);
  DEFINE_IN_PLACE_METHODS(EVP_sha384(), SHA384);
  DEFINE_IN_PLACE_METHODS(EVP_sha512(), SHA512);
  DEFINE_IN_PLACE_METHODS(EVP_sha512_256(), SHA512_256);
}

OPENSSL_STATIC_ASSERT(sizeof(((struct hmac_method_array_st *)NULL)->methods) <=
                      HMAC_METHOD_MAX * sizeof(struct hmac_methods_st),
                      hmac_methods_to_short_for_loop_limits_t)
static const HmacMethods *GetInPlaceMethods(const EVP_MD *evp_md) {
  const HmacMethods *methods = AWSLC_hmac_in_place_methods()->methods;
  for (size_t idx = 0; idx < HMAC_METHOD_MAX; idx++) {
    if (methods[idx].evp_md == evp_md) {
      return &methods[idx];
    }
  }
  return NULL;
}

uint8_t *HMAC(const EVP_MD *evp_md, const void *key, size_t key_len,
              const uint8_t *data, size_t data_len, uint8_t *out,
              unsigned int *out_len) {
  // We have to avoid the underlying SHA services updating the indicator
  // state, so we lock the state here.
  FIPS_service_indicator_lock_state();
  HMAC_CTX ctx = {.initialized = 0};
  int result;
  // If out is NULL, the digest is placed in a static array.
  // Note: passing a NULL value for out to use the static array is not thread safe.
  static uint8_t fallback_output[EVP_MAX_MD_SIZE] = {0};
  if (out == NULL) {
    out = fallback_output;
  }

  result = HMAC_Init_ex(&ctx, key, key_len, evp_md, NULL) &&
           HMAC_Update(&ctx, data, data_len) &&
           HMAC_Final(&ctx, out, out_len);
  FIPS_service_indicator_unlock_state();
  HMAC_CTX_cleanup(&ctx);
  if (result) {
    HMAC_verify_service_indicator(evp_md);
    return out;
  } else {
    OPENSSL_cleanse(out, EVP_MD_size(evp_md));
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
  assert(impl == NULL);

  // ctx->initialized has 4 possible states (Pre/Post conditions)
  // 0: Uninitialized.
  // 1: Initialized with an md and key (all fields of ctx are ready for use and non-null)
  // other: Invalid state and likely a result of using unitialized memory. Treated the same as 0.
  //
  // While we are within this method we allow these other possible states:
  // -1: We have md and methods assigned but the key needs to be set up
  if (md && ctx->md != md) {
    ctx->methods = GetInPlaceMethods(md);
    if (ctx->methods == NULL) {
      // Unsupported md
      return 0;
    }
    ctx->md = md;
    ctx->initialized = -1; // We need to rekey so initialized != 1
  } else if (ctx->initialized != 1) {
    // We are not initialized but have not been provided with an md to initialize ourselves with.
    return 0;
  }

  // At this point we know we have valid methods and a context allocated.
  const HmacMethods *methods = ctx->methods;
  size_t block_size = EVP_MD_block_size(methods->evp_md);
  assert(block_size % 8 == 0);
  assert(block_size <= EVP_MAX_MD_BLOCK_SIZE);

  // We have to avoid the underlying SHA services updating the indicator
  // state, so we lock the state here.
  FIPS_service_indicator_lock_state();
  int result = 0;

  // If either |key| is non-NULL or |md| has changed (indicated by initialized != 1), initialize with a new key
  // rather than rewinding the previous one.
  //
  // TODO(davidben,eroman): Passing the previous |md| with a NULL |key| is
  // ambiguous between using the empty key and reusing the previous key. There
  // exist callers which intend the latter, but the former is an awkward edge
  // case. Fix to API to avoid this.
  if (key != NULL || ctx->initialized != 1) {
    uint64_t pad[EVP_MAX_MD_BLOCK_SIZE / 8] = {0};
    uint64_t key_block[EVP_MAX_MD_BLOCK_SIZE / 8] = {0};
    if (block_size < key_len) {
      // Long keys are hashed.
      if (!methods->init(&ctx->md_ctx) ||
          !methods->update(&ctx->md_ctx, key, key_len) ||
          !methods->finalize((uint8_t *) key_block, &ctx->md_ctx)) {
        goto end;
      }
    } else {
      assert(key_len <= sizeof(key_block));
      OPENSSL_memcpy(key_block, key, key_len);
    }
    for (size_t i = 0; i < block_size / 8; i++) {
      pad[i] = 0x3636363636363636 ^ key_block[i];
    }
    if (!methods->init(&ctx->i_ctx) ||
        !methods->update(&ctx->i_ctx, pad, block_size)) {
      goto end;
    }
    for (size_t i = 0; i < block_size / 8; i++) {
      pad[i] = 0x5c5c5c5c5c5c5c5c ^ key_block[i];
    }
    if (!methods->init(&ctx->o_ctx) ||
        !methods->update(&ctx->o_ctx, pad, block_size)) {
      goto end;
    }
    ctx->initialized = 1;
  }
  OPENSSL_memcpy(&ctx->md_ctx, &ctx->i_ctx, sizeof(ctx->i_ctx));
  result = 1;
end:
  FIPS_service_indicator_unlock_state();
  return result;
}

int HMAC_Update(HMAC_CTX *ctx, const uint8_t *data, size_t data_len) {
  const HmacMethods *methods = ctx->methods;
  if (methods == NULL || ctx->initialized != 1) {
    return 0;
  }
  return methods->update(&ctx->md_ctx, data, data_len);
}

int HMAC_Final(HMAC_CTX *ctx, uint8_t *out, unsigned int *out_len) {
  const HmacMethods *methods = ctx->methods;
  if (methods == NULL || ctx->initialized != 1) {
    return 0;
  }
  // We have to avoid the underlying SHA services updating the indicator
  // state, so we lock the state here.
  FIPS_service_indicator_lock_state();
  int result = 0;
  const EVP_MD *evp_md = ctx->md;
  int hmac_len = EVP_MD_size(evp_md);
  uint8_t tmp[EVP_MAX_MD_SIZE];
  if (!methods->finalize(tmp, &ctx->md_ctx)) {
    goto end;
  }
  OPENSSL_memcpy(&ctx->md_ctx, &ctx->o_ctx, sizeof(ctx->o_ctx));
  if (!ctx->methods->update(&ctx->md_ctx, tmp, hmac_len)) {
    goto end;
  }
  result = methods->finalize(out, &ctx->md_ctx);
  OPENSSL_cleanse(&ctx->md_ctx, sizeof(ctx->md_ctx));
end:
  FIPS_service_indicator_unlock_state();
  if (result) {
    HMAC_verify_service_indicator(evp_md);
    if (out_len) {
      *out_len = hmac_len;
    }
    return 1;
  } else {
    if (out_len) {
      *out_len = 0;
    }
    return 0;
  }
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
