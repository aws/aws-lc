// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

#ifndef AWSLC_PROVIDER_PROVIDER_H
#define AWSLC_PROVIDER_PROVIDER_H

// Shared between the provider's OpenSSL-facing files.

#include <openssl/core.h>
#include <openssl/core_dispatch.h>

#include "internal/backend.h"

#if defined(__cplusplus)
extern "C" {
#endif

// The property strings every algorithm we register carries.
#define AWSLC_PROV_PROPERTIES "provider=awslc"
// Apply fips=yes to algorithms that AWS-LC can approve in FIPS mode.
#define AWSLC_PROV_FIPS_PROPERTIES AWSLC_PROV_PROPERTIES ",fips=yes"

// AWSLC_PROV_CTX is the per-load provider context.
typedef struct awslc_prov_ctx_st AWSLC_PROV_CTX;

// The core handle for this load, used when raising errors back to the core.
const OSSL_CORE_HANDLE *awslc_prov_ctx_handle(const AWSLC_PROV_CTX *ctx);

// The core upcalls this provider uses, captured at init.
typedef struct {
  // OPENSSL_CORE_CTX *(const OSSL_CORE_HANDLE *prov)
  // The opaque core context for this load, which the indicator upcall is
  // addressed to.
  OSSL_FUNC_core_get_libctx_fn *get_libctx;

  // void (OPENSSL_CORE_CTX *ctx, OSSL_INDICATOR_CALLBACK **cb)
  // Fetches the application's FIPS indicator callback, or leaves |cb| NULL.
  OSSL_FUNC_indicator_cb_fn *indicator_cb;

  // void (const OSSL_CORE_HANDLE *prov)
  // Opens a new record on the caller's error queue.
  OSSL_FUNC_core_new_error_fn *new_error;

  // void (const OSSL_CORE_HANDLE *prov, const char *file, int line,
  //       const char *func)
  // Attaches origin metadata to the open record.
  OSSL_FUNC_core_set_error_debug_fn *set_error_debug;

  // void (const OSSL_CORE_HANDLE *prov, uint32_t reason, const char *fmt,
  //       va_list args)
  // Sets the reason and formatted detail on the open record. Unlike
  // the other two error upcalls it reads |prov| to find the error library to file
  // under, so it cannot be passed NULL.
  OSSL_FUNC_core_vset_error_fn *vset_error;
} AWSLC_PROV_UPCALLS;

// NULL for a NULL |ctx|, which is what makes raising without a context a no-op
// rather than a crash.
const AWSLC_PROV_UPCALLS *awslc_prov_ctx_upcalls(const AWSLC_PROV_CTX *ctx);

// Whether the linked AWS-LC reported FIPS mode when this provider initialized.
int awslc_prov_ctx_is_fips(const AWSLC_PROV_CTX *ctx);

// Notify the application through the provider context |ctx| that a fips=yes
// operation completed without an approved verdict. |type| contains the
// algorithm type and |description| contains the operation that is not approved.
// A missing callback permits the result; a callback may veto it by returning
// zero.
int awslc_prov_indicator_on_unapproved(AWSLC_PROV_CTX *ctx, const char *type,
                                       const char *description);

// The fan-out, implemented in registry.c and published by provider.c in the
// top-level dispatch table. The dispatch tables it hands out are declared in
// per-class headers, which only registry.c and the class implementations include.
const OSSL_ALGORITHM *awslc_prov_query_operation(void *provctx, int operation_id,
                                                 int *no_store);

// Error reporting, implemented in errors.c. The reason namespace is in
// internal/backend.h.

// The reason-string table for the provider's private error library, published by
// provider.c in the top-level dispatch table.
OSSL_FUNC_provider_get_reason_strings_fn awslc_prov_get_reason_strings;

// Raise one error from the provider layer itself. |detail| is optional
// per-occurrence text.
void awslc_prov_error_raise(const AWSLC_PROV_CTX *ctx, uint32_t reason,
                            const char *file, int line, const char *detail);

// Raise at the call site's own file and line.
#define AWSLC_PROV_ERROR_RAISE(ctx, reason, detail) \
  awslc_prov_error_raise((ctx), (reason), __FILE__, __LINE__, (detail))

// Every dispatch slot that calls into AWS-LC brackets those calls, handing its own
// result to the macro below and returning what the macro returns:
//
//   awslc_prov_error_mark();
//   ok = <one or more backend calls>;
//   return AWSLC_PROV_ERROR_SETTLE(ctx->provctx, ok, AWSLC_PROV_R_BACKEND_ERROR,
//                                  ctx->algorithm_name);
//
// |succeeded| comes back unchanged, and the AWS-LC queue is left empty either way:
//
//   true    Discard. AWS-LC queues records on recoverable internal paths that a
//           successful call must not leak to the application.
//   false   Translate AWS-LC's records onto OpenSSL's queue, oldest first, or
//           raise |reason| and |detail| if AWS-LC queued none, so a failed call
//           never leaves the queue empty.
int awslc_prov_error_settle(const AWSLC_PROV_CTX *ctx, int succeeded,
                            uint32_t reason, const char *file, int line,
                            const char *detail);

#define AWSLC_PROV_ERROR_SETTLE(ctx, succeeded, reason, detail)          \
  awslc_prov_error_settle((ctx), (succeeded), (reason), __FILE__, __LINE__, \
                          (detail))

#if defined(__cplusplus)
}  // extern "C"
#endif

#endif  // AWSLC_PROVIDER_PROVIDER_H
