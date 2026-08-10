// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Front side: SHA-256's dispatch slots and their OSSL_PARAM plumbing. This file
// sees OpenSSL's headers, so it must not include any AWS-LC header; the transform
// arrives through the backend interface.
//
// Each slot is declared through its own OSSL_FUNC_digest_*_fn typedef so its
// signature is checked against what the core calls it with, rather than only
// against the (void (*)(void)) cast in the dispatch table, which would erase a
// drift to a neighbouring slot's shape.

#include <openssl/core_dispatch.h>
#include <openssl/core_names.h>
#include <openssl/params.h>

#include "internal/backend.h"
#include "internal/backend/digests.h"
#include "internal/frontend/digests.h"

static OSSL_FUNC_digest_newctx_fn awslc_prov_sha256_newctx;
static OSSL_FUNC_digest_freectx_fn awslc_prov_sha256_freectx;
static OSSL_FUNC_digest_dupctx_fn awslc_prov_sha256_dupctx;
static OSSL_FUNC_digest_copyctx_fn awslc_prov_sha256_copyctx;
static OSSL_FUNC_digest_init_fn awslc_prov_sha256_init_op;
static OSSL_FUNC_digest_update_fn awslc_prov_sha256_update_op;
static OSSL_FUNC_digest_final_fn awslc_prov_sha256_final_op;
static OSSL_FUNC_digest_get_params_fn awslc_prov_sha256_get_params;
static OSSL_FUNC_digest_gettable_params_fn awslc_prov_sha256_gettable_params;

static void *awslc_prov_sha256_newctx(void *provctx) {
  (void)provctx;
  return awslc_prov_zalloc(awslc_prov_sha256_ctx_size());
}

static void awslc_prov_sha256_freectx(void *dctx) {
  if (dctx == NULL) {
    return;
  }
  awslc_prov_clear_free(dctx, awslc_prov_sha256_ctx_size());
}

static void *awslc_prov_sha256_dupctx(void *dctx) {
  void *duplicate;

  if (dctx == NULL) {
    return NULL;
  }
  duplicate = awslc_prov_zalloc(awslc_prov_sha256_ctx_size());
  if (duplicate == NULL) {
    return NULL;
  }
  awslc_prov_sha256_copy(duplicate, dctx);
  return duplicate;
}

static void awslc_prov_sha256_copyctx(void *outctx, void *inctx) {
  if (outctx == NULL || inctx == NULL) {
    return;
  }
  awslc_prov_sha256_copy(outctx, inctx);
}

static int awslc_prov_sha256_init_op(void *dctx, const OSSL_PARAM params[]) {
  (void)params;
  if (dctx == NULL) {
    return 0;
  }
  return awslc_prov_sha256_init(dctx);
}

static int awslc_prov_sha256_update_op(void *dctx, const unsigned char *in,
                                       size_t inl) {
  if (dctx == NULL) {
    return 0;
  }
  // A zero-length update with a NULL pointer is legal and must be a no-op rather
  // than reaching the backend with a NULL buffer.
  if (inl == 0) {
    return 1;
  }
  if (in == NULL) {
    return 0;
  }
  return awslc_prov_sha256_update(dctx, in, inl);
}

static int awslc_prov_sha256_final_op(void *dctx, unsigned char *out,
                                      size_t *outl, size_t outsz) {
  if (dctx == NULL || out == NULL || outl == NULL) {
    return 0;
  }
  // The backend enforces outsz against the digest length, because AWS-LC's
  // SHA256_Final takes no size argument and would write past a short buffer.
  if (!awslc_prov_sha256_final(dctx, out, outsz)) {
    return 0;
  }
  *outl = awslc_prov_sha256_digest_size();
  return 1;
}

static const OSSL_PARAM awslc_prov_sha256_gettable[] = {
    OSSL_PARAM_size_t(OSSL_DIGEST_PARAM_BLOCK_SIZE, NULL),
    OSSL_PARAM_size_t(OSSL_DIGEST_PARAM_SIZE, NULL),
    OSSL_PARAM_int(OSSL_DIGEST_PARAM_XOF, NULL),
    OSSL_PARAM_int(OSSL_DIGEST_PARAM_ALGID_ABSENT, NULL),
    OSSL_PARAM_END};

static const OSSL_PARAM *awslc_prov_sha256_gettable_params(void *provctx) {
  (void)provctx;
  return awslc_prov_sha256_gettable;
}

static int awslc_prov_sha256_get_params(OSSL_PARAM params[]) {
  OSSL_PARAM *p;

  p = OSSL_PARAM_locate(params, OSSL_DIGEST_PARAM_BLOCK_SIZE);
  if (p != NULL && !OSSL_PARAM_set_size_t(p, awslc_prov_sha256_block_size())) {
    return 0;
  }
  p = OSSL_PARAM_locate(params, OSSL_DIGEST_PARAM_SIZE);
  if (p != NULL && !OSSL_PARAM_set_size_t(p, awslc_prov_sha256_digest_size())) {
    return 0;
  }
  // Not an extendable-output function, so a caller asking for a length of its own
  // choosing must be refused rather than served a truncated digest.
  p = OSSL_PARAM_locate(params, OSSL_DIGEST_PARAM_XOF);
  if (p != NULL && !OSSL_PARAM_set_int(p, 0)) {
    return 0;
  }
  // An AlgorithmIdentifier is the ASN.1 structure naming a digest inside DER: an
  // OID plus an OPTIONAL parameters field. Hashes take no parameters, so 1 means
  // "omit that field entirely" while 0 means "include it holding an explicit
  // NULL". Both are valid DER, so this has to match what everyone else emits: 1
  // is correct for SHA-2 and is what OpenSSL's own SHA-2 reports, and reporting 0
  // would make our CMS and RSA DigestInfo encodings differ from the default
  // provider's by a trailing 05 00.
  p = OSSL_PARAM_locate(params, OSSL_DIGEST_PARAM_ALGID_ABSENT);
  if (p != NULL && !OSSL_PARAM_set_int(p, 1)) {
    return 0;
  }
  return 1;
}

const OSSL_DISPATCH awslc_prov_sha256_functions[] = {
    {OSSL_FUNC_DIGEST_NEWCTX, (void (*)(void))awslc_prov_sha256_newctx},
    {OSSL_FUNC_DIGEST_INIT, (void (*)(void))awslc_prov_sha256_init_op},
    {OSSL_FUNC_DIGEST_UPDATE, (void (*)(void))awslc_prov_sha256_update_op},
    {OSSL_FUNC_DIGEST_FINAL, (void (*)(void))awslc_prov_sha256_final_op},
    {OSSL_FUNC_DIGEST_FREECTX, (void (*)(void))awslc_prov_sha256_freectx},
    {OSSL_FUNC_DIGEST_DUPCTX, (void (*)(void))awslc_prov_sha256_dupctx},
    {OSSL_FUNC_DIGEST_COPYCTX, (void (*)(void))awslc_prov_sha256_copyctx},
    {OSSL_FUNC_DIGEST_GET_PARAMS, (void (*)(void))awslc_prov_sha256_get_params},
    {OSSL_FUNC_DIGEST_GETTABLE_PARAMS,
     (void (*)(void))awslc_prov_sha256_gettable_params},
    OSSL_DISPATCH_END};
