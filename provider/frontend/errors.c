// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// Front side: reporting into OpenSSL's error queue under the provider's private
// error library.

#include <openssl/core.h>
#include <openssl/core_dispatch.h>

#include <stdarg.h>

#include "internal/backend.h"
#include "internal/provider.h"

// Statically define reason strings for the provider's private reason codes.
static const OSSL_ITEM awslc_prov_reason_strings[] = {
    {AWSLC_PROV_R_BACKEND_ERROR, (void *)"AWS-LC reported a failure"},
    {AWSLC_PROV_R_INVALID_PARAMETER, (void *)"invalid parameter"},
    {AWSLC_PROV_R_UNAPPROVED_OPERATION, (void *)"unapproved operation"},
    {0, NULL}};

const OSSL_ITEM *awslc_prov_get_reason_strings(void *provctx) {
  (void)provctx;
  return awslc_prov_reason_strings;
}

// core_vset_error takes a va_list, so the variadic stack frame is built here.
static void awslc_prov_vset_error(OSSL_FUNC_core_vset_error_fn *vset_error,
                                  const OSSL_CORE_HANDLE *handle,
                                  uint32_t reason, const char *fmt, ...) {
  va_list args;

  va_start(args, fmt);
  vset_error(handle, reason, fmt, args);
  va_end(args);
}

void awslc_prov_error_raise(const AWSLC_PROV_CTX *ctx, uint32_t reason,
                            const char *file, int line, const char *detail) {
  const AWSLC_PROV_UPCALLS *upcalls = awslc_prov_ctx_upcalls(ctx);
  const OSSL_CORE_HANDLE *handle = NULL;

  if (upcalls == NULL) {
    return;
  }
  // core_vset_error reads |handle| for the library id to file under, so unlike the
  // other two upcalls it cannot be passed NULL.
  handle = awslc_prov_ctx_handle(ctx);

  upcalls->new_error(handle);
  // AWS-LC records no function name, so OpenSSL's slot for one stays empty.
  upcalls->set_error_debug(handle, file, line, NULL);
  if (detail == NULL || detail[0] == '\0') {
    awslc_prov_vset_error(upcalls->vset_error, handle, reason, NULL);
  } else {
    // "%s", not |detail| itself, which is data and can contain a percent sign.
    awslc_prov_vset_error(upcalls->vset_error, handle, reason, "%s", detail);
  }
}

// Re-raise AWS-LC's records oldest first and return how many came off the queue.
// Zero means the back side queued nothing.
static size_t awslc_prov_error_flush(const AWSLC_PROV_CTX *ctx) {
  AWSLC_PROV_ERROR record;
  size_t drained = 0;

  while (awslc_prov_error_shift(&record)) {
    awslc_prov_error_raise(ctx, record.reason, record.file, record.line,
                           record.detail);
    drained++;
  }
  return drained;
}

int awslc_prov_error_settle(const AWSLC_PROV_CTX *ctx, int succeeded,
                            uint32_t reason, const char *file, int line,
                            const char *detail) {
  if (succeeded) {
    awslc_prov_error_discard();
    return succeeded;
  }
  // A failed dispatch call must never leave the queue empty, or the caller cannot
  // tell a lost cause from no cause. Backend paths that queue nothing, and the
  // provider's own checks, fall back to the slot's reason.
  if (awslc_prov_error_flush(ctx) == 0) {
    awslc_prov_error_raise(ctx, reason, file, line, detail);
  }
  return succeeded;
}
