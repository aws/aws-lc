// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Front side: SHA-2 dispatch slots and OSSL_PARAM plumbing.
//
// Shared behavior is ordinary C at the family level. Each algorithm then has
// thin, typed wrappers naming its own backend entry points.

#include "internal/backend.h"
#include "internal/backend/digests.h"
#include "internal/frontend/digests.h"

// Changes the DER OpenSSL emits for this digest inside PKI structures. The value
// must match the OpenSSL default provider's, or our encodings differ from it.
#define AWSLC_PROV_SHA2_FLAGS AWSLC_PROV_DIGEST_FLAG_ALGID_ABSENT

typedef int (*awslc_prov_sha2_init_fn)(void *ctx);
typedef int (*awslc_prov_sha2_update_fn)(void *ctx, const void *data,
                                         size_t len);
typedef int (*awslc_prov_sha2_final_fn)(void *ctx, unsigned char *out,
                                        size_t out_size);
typedef int (*awslc_prov_sha2_copy_fn)(void *dst, const void *src);

static void awslc_prov_sha2_freectx(void *dctx, size_t ctx_size) {
  if (dctx == NULL) {
    return;
  }
  awslc_prov_clear_free(dctx, ctx_size);
}

static void *awslc_prov_sha2_dupctx(void *dctx, size_t ctx_size,
                                    awslc_prov_sha2_copy_fn copy) {
  void *duplicate = NULL;

  if (dctx == NULL) {
    return NULL;
  }
  duplicate = awslc_prov_zalloc(ctx_size);
  if (duplicate == NULL) {
    return NULL;
  }
  if (!copy(duplicate, dctx)) {
    awslc_prov_clear_free(duplicate, ctx_size);
    return NULL;
  }
  return duplicate;
}

static void awslc_prov_sha2_copyctx(void *outctx, void *inctx,
                                    awslc_prov_sha2_copy_fn copy) {
  if (outctx == NULL || inctx == NULL) {
    return;
  }
  (void)copy(outctx, inctx);
}

// The init params are forwarded signature-operation params, not a digest-scoped
// array. No digest can honor keys such as pad-mode or saltlen, so ignore them.
static int awslc_prov_sha2_init_op(void *dctx, const OSSL_PARAM params[],
                                   awslc_prov_sha2_init_fn init) {
  (void)params;
  if (dctx == NULL) {
    return 0;
  }
  return init(dctx);
}

static int awslc_prov_sha2_update_op(void *dctx, const unsigned char *in,
                                     size_t inl,
                                     awslc_prov_sha2_update_fn update) {
  if (dctx == NULL) {
    return 0;
  }
  // A zero-length update with a NULL |in| is legal per the EVP contract. AWS-LC
  // already treats len == 0 as a no-op, so this is a guard against a future
  // backend that does not, not a workaround for the current one.
  if (inl == 0) {
    return 1;
  }
  if (in == NULL) {
    return 0;
  }
  return update(dctx, in, inl);
}

static int awslc_prov_sha2_final_op(void *dctx, unsigned char *out, size_t *outl,
                                    size_t outsz,
                                    awslc_prov_sha2_final_fn final_fn,
                                    size_t digest_size) {
  if (dctx == NULL || out == NULL || outl == NULL) {
    return 0;
  }
  if (!final_fn(dctx, out, outsz)) {
    return 0;
  }
  *outl = digest_size;
  return 1;
}

static int awslc_prov_sha2_get_params(OSSL_PARAM params[],
                                      size_t block_size, size_t digest_size) {
  return awslc_prov_digest_get_params(params, block_size, digest_size,
                                      AWSLC_PROV_SHA2_FLAGS);
}

// SHA-224

AWSLC_PROV_DECLARE_FIXED_DIGEST_SLOTS(sha224);

static void *awslc_prov_sha224_newctx(void *provctx) {
  (void)provctx;
  return awslc_prov_zalloc(awslc_prov_sha224_ctx_size());
}

static void awslc_prov_sha224_freectx(void *dctx) {
  awslc_prov_sha2_freectx(dctx, awslc_prov_sha224_ctx_size());
}

static void *awslc_prov_sha224_dupctx(void *dctx) {
  return awslc_prov_sha2_dupctx(dctx, awslc_prov_sha224_ctx_size(),
                                awslc_prov_sha224_copy);
}

static void awslc_prov_sha224_copyctx(void *outctx, void *inctx) {
  awslc_prov_sha2_copyctx(outctx, inctx, awslc_prov_sha224_copy);
}

static int awslc_prov_sha224_init_op(void *dctx, const OSSL_PARAM params[]) {
  return awslc_prov_sha2_init_op(dctx, params, awslc_prov_sha224_init);
}

static int awslc_prov_sha224_update_op(void *dctx, const unsigned char *in,
                                       size_t inl) {
  return awslc_prov_sha2_update_op(dctx, in, inl, awslc_prov_sha224_update);
}

static int awslc_prov_sha224_final_op(void *dctx, unsigned char *out,
                                      size_t *outl, size_t outsz) {
  return awslc_prov_sha2_final_op(dctx, out, outl, outsz,
                                  awslc_prov_sha224_final,
                                  awslc_prov_sha224_digest_size());
}

static int awslc_prov_sha224_get_params(OSSL_PARAM params[]) {
  return awslc_prov_sha2_get_params(params, awslc_prov_sha224_block_size(),
                                    awslc_prov_sha224_digest_size());
}

AWSLC_PROV_FIXED_DIGEST_DISPATCH_TABLE(sha224);

// SHA-256

AWSLC_PROV_DECLARE_FIXED_DIGEST_SLOTS(sha256);

static void *awslc_prov_sha256_newctx(void *provctx) {
  (void)provctx;
  return awslc_prov_zalloc(awslc_prov_sha256_ctx_size());
}

static void awslc_prov_sha256_freectx(void *dctx) {
  awslc_prov_sha2_freectx(dctx, awslc_prov_sha256_ctx_size());
}

static void *awslc_prov_sha256_dupctx(void *dctx) {
  return awslc_prov_sha2_dupctx(dctx, awslc_prov_sha256_ctx_size(),
                                awslc_prov_sha256_copy);
}

static void awslc_prov_sha256_copyctx(void *outctx, void *inctx) {
  awslc_prov_sha2_copyctx(outctx, inctx, awslc_prov_sha256_copy);
}

static int awslc_prov_sha256_init_op(void *dctx, const OSSL_PARAM params[]) {
  return awslc_prov_sha2_init_op(dctx, params, awslc_prov_sha256_init);
}

static int awslc_prov_sha256_update_op(void *dctx, const unsigned char *in,
                                       size_t inl) {
  return awslc_prov_sha2_update_op(dctx, in, inl, awslc_prov_sha256_update);
}

static int awslc_prov_sha256_final_op(void *dctx, unsigned char *out,
                                      size_t *outl, size_t outsz) {
  return awslc_prov_sha2_final_op(dctx, out, outl, outsz,
                                  awslc_prov_sha256_final,
                                  awslc_prov_sha256_digest_size());
}

static int awslc_prov_sha256_get_params(OSSL_PARAM params[]) {
  return awslc_prov_sha2_get_params(params, awslc_prov_sha256_block_size(),
                                    awslc_prov_sha256_digest_size());
}

AWSLC_PROV_FIXED_DIGEST_DISPATCH_TABLE(sha256);
