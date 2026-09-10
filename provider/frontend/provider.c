// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// The provider-global surface: OSSL_provider_init, the top-level dispatch table,
// and the parameters the provider answers about itself. What it advertises is
// registry.c.

#include <openssl/core.h>
#include <openssl/core_dispatch.h>
#include <openssl/core_names.h>
#include <openssl/params.h>

#include "internal/backend.h"
#include "internal/provider.h"

// The provider carries its own Semantic Versioning line, independent of the
// AWS-LC release it links.
#define AWSLC_PROV_VERSION "0.1.0"
#define AWSLC_PROV_NAME "AWS-LC Provider"

// OSSL_provider_init is the only symbol the module exports; everything else is
// hidden. OpenSSL's own OPENSSL_EXPORT expands to plain `extern` on ELF and
// Mach-O, which would not survive -fvisibility=hidden, so the visibility is
// stated here directly.
#if defined(_WIN32)
#define AWSLC_PROV_ENTRY __declspec(dllexport)
#else
#define AWSLC_PROV_ENTRY __attribute__((visibility("default")))
#endif

struct awslc_prov_ctx_st {
  const OSSL_CORE_HANDLE *handle;
  OPENSSL_CORE_CTX *corectx;
};

const OSSL_CORE_HANDLE *awslc_prov_ctx_handle(const AWSLC_PROV_CTX *ctx) {
  return ctx->handle;
}

// Parameters we answer about ourselves.
static const OSSL_PARAM awslc_prov_param_types[] = {
    OSSL_PARAM_DEFN(OSSL_PROV_PARAM_NAME, OSSL_PARAM_UTF8_PTR, NULL, 0),
    OSSL_PARAM_DEFN(OSSL_PROV_PARAM_VERSION, OSSL_PARAM_UTF8_PTR, NULL, 0),
    OSSL_PARAM_DEFN(OSSL_PROV_PARAM_BUILDINFO, OSSL_PARAM_UTF8_PTR, NULL, 0),
    OSSL_PARAM_DEFN(OSSL_PROV_PARAM_STATUS, OSSL_PARAM_INTEGER, NULL, 0),
    OSSL_PARAM_END};

static const OSSL_PARAM *awslc_prov_gettable_params(void *provctx) {
  (void)provctx;
  return awslc_prov_param_types;
}

static int awslc_prov_get_params(void *provctx, OSSL_PARAM params[]) {
  AWSLC_PROV_CTX *ctx = (AWSLC_PROV_CTX *)provctx;
  OSSL_PARAM *p = NULL;

  if (ctx == NULL) {
    return 0;
  }

  p = OSSL_PARAM_locate(params, OSSL_PROV_PARAM_NAME);
  if (p != NULL && !OSSL_PARAM_set_utf8_ptr(p, AWSLC_PROV_NAME)) {
    return 0;
  }
  p = OSSL_PARAM_locate(params, OSSL_PROV_PARAM_VERSION);
  if (p != NULL && !OSSL_PARAM_set_utf8_ptr(p, AWSLC_PROV_VERSION)) {
    return 0;
  }
  p = OSSL_PARAM_locate(params, OSSL_PROV_PARAM_BUILDINFO);
  if (p != NULL &&
      !OSSL_PARAM_set_utf8_ptr(p, awslc_prov_backend_version())) {
    return 0;
  }
  p = OSSL_PARAM_locate(params, OSSL_PROV_PARAM_STATUS);
  // Constant-true once loaded. AWS-LC aborts the process if a FIPS self-test
  // fails, so unlike OpenSSL's FIPS module there is no refusing-but-alive state
  // for this to report.
  if (p != NULL && !OSSL_PARAM_set_int(p, 1)) {
    return 0;
  }
  return 1;
}

static void awslc_prov_teardown(void *provctx) {
  AWSLC_PROV_CTX *ctx = (AWSLC_PROV_CTX *)provctx;

  if (ctx == NULL) {
    return;
  }
  awslc_prov_clear_free(ctx, sizeof(*ctx));
}

// Functions we provide to the core.
static const OSSL_DISPATCH awslc_prov_dispatch_table[] = {
    {OSSL_FUNC_PROVIDER_TEARDOWN, (void (*)(void))awslc_prov_teardown},
    {OSSL_FUNC_PROVIDER_GETTABLE_PARAMS,
     (void (*)(void))awslc_prov_gettable_params},
    {OSSL_FUNC_PROVIDER_GET_PARAMS, (void (*)(void))awslc_prov_get_params},
    {OSSL_FUNC_PROVIDER_QUERY_OPERATION,
     (void (*)(void))awslc_prov_query_operation},
    OSSL_DISPATCH_END};

// Entry point for the entire provider.
AWSLC_PROV_ENTRY int OSSL_provider_init(const OSSL_CORE_HANDLE *handle,
                                        const OSSL_DISPATCH *in,
                                        const OSSL_DISPATCH **out,
                                        void **provctx) {
  OSSL_FUNC_core_get_libctx_fn *c_get_libctx = NULL;
  AWSLC_PROV_CTX *ctx = NULL;

  // Scan the upcalls the core offers and keep the ones we use. Unrecognized ids
  // are skipped, which is what keeps this forward-compatible as the core adds
  // upcalls we do not know about.
  for (; in->function_id != 0; in++) {
    switch (in->function_id) {
      case OSSL_FUNC_CORE_GET_LIBCTX:
        c_get_libctx = OSSL_FUNC_core_get_libctx(in);
        break;
      default:
        break;
    }
  }

  // Without a libctx we cannot guarantee that calls we make land in the same
  // library context the core called us with, so refuse to load rather than
  // guess.
  if (c_get_libctx == NULL) {
    return 0;
  }

  ctx = awslc_prov_zalloc(sizeof(*ctx));
  if (ctx == NULL) {
    return 0;
  }
  ctx->handle = handle;
  ctx->corectx = c_get_libctx(handle);

  *provctx = ctx;
  *out = awslc_prov_dispatch_table;
  return 1;
}
